# -*- coding: utf-8 -*-
"""
死代码检测（Dead Code Analysis）。

在已通过词法 / 语法分析的 AST 上做一遍**可达性分析**，找出控制流意义上
永远执行不到的语句。判定基于现有的 AST 控制流结构与轻量的常量表达式求值
（语义层同款字面量/运算规则），不引入任何新的依赖：

  * 无条件 ``return`` / ``break`` / ``continue`` 之后顺序排列的语句；
  * 恒假分支：``if (false) { ... }`` / 不可达的 ``elif`` 分支；
  * 恒真条件之后的 ``else`` 分支（``if (true) { ... } else { ... }``）；
  * 恒假循环：``while (false) { ... }`` / ``for (...; false; ...)`` 的循环体；
  * 支持嵌套分支、循环以及独立分析每个函数体。

可达性用一个三态"出口位掩码"在语句序列上传播：
  * NORMAL   —— 能顺序走到语句之后；
  * RETURN   —— 以 return 离开（其后的顺序语句不可达）；
  * BREAK / CONTINUE —— 以 break / continue 离开（只在所属循环内有效）。
无法静态求值的条件一律按"两个方向都可能"处理，因此正常代码不会被误标。

检测产出两部分（供编辑器与诊断页复用）：
  * ``Diagnostic``（severity=warning, phase=deadcode），每段连续不可达区域一条；
  * ``DeadRegion`` 列表（行区间 + 原因），供编辑器做整行高亮。
"""

from dataclasses import dataclass
from typing import List, Optional, Tuple

from . import ast_nodes as ast
from .diagnostics import (
    DiagnosticBag, Diagnostic,
    SEVERITY_WARNING, KIND_SYNTAX,
)

PHASE_DEADCODE = "deadcode"

# 出口位掩码
NORMAL = 1 << 0
RETURN = 1 << 1
BREAK = 1 << 2
CONTINUE = 1 << 3
INFINITE = 1 << 4   # 恒真且无 break 的循环：永远不会结束


# ---------------------------------------------------------------------------
# 检测结果
# ---------------------------------------------------------------------------
@dataclass
class DeadRegion:
    """一段连续的不可达源码区域（行号 1-based，闭区间）。"""
    start_line: int
    end_line: int
    reason: str
    message: str

    def to_dict(self):
        return {
            "start_line": self.start_line,
            "end_line": self.end_line,
            "reason": self.reason,
            "message": self.message,
        }


# ---------------------------------------------------------------------------
# 轻量常量求值
# ---------------------------------------------------------------------------
class _Unknown:
    """无法静态求值的哨兵单例（标识符、调用、下标等）。"""


UNKNOWN = _Unknown()


def _truthy(value) -> Optional[bool]:
    """与 runtime.truthy 一致的真值判定；无法确定时返回 None。"""
    if value is UNKNOWN:
        return None
    # MiniLang 真值规则：null 与 false 为假，其余（含 0、""、[]）为真
    if value is None or value is False:
        return False
    return True


def static_truth(e) -> Optional[bool]:
    """静态判定一个布尔上下文里表达式的真假；无法确定返回 None。

    比完整常量求值更宽松：利用 && / || 的短路性质，只要一侧的真值
    恒定，整个表达式的真假即可确定（另一侧可能含动态变量也没关系）。
    """
    tv = _truthy(const_eval(e))
    if tv is not None:
        return tv
    if isinstance(e, ast.LogicalExpr):
        lt = _truthy(const_eval(e.left))
        rt = static_truth(e.right)
        if e.op == "&&":
            # false && X => false；X && false => false；X && true => 取决于 X
            if lt is False or rt is False:
                return False
            if lt is True and rt is True:
                return True
        else:  # ||
            # true || X => true；X || true => true；X || false => 取决于 X
            if lt is True or rt is True:
                return True
            if lt is False and rt is False:
                return False
    return None


def const_eval(e):
    """尽力对常量表达式求值；任何动态成分都退化为 UNKNOWN。"""
    if e is None:
        return UNKNOWN
    if isinstance(e, ast.BoolLiteral):
        return e.value
    if isinstance(e, ast.NullLiteral):
        return None
    if isinstance(e, ast.NumberLiteral):
        return e.value
    if isinstance(e, ast.StringLiteral):
        return e.value
    if isinstance(e, ast.UnaryExpr):
        v = const_eval(e.operand)
        if v is UNKNOWN:
            return UNKNOWN
        if e.op == "!":
            # 与 VM 一致：null / false 为假
            return not (v is not None and v is not False)
        if e.op == "-" and isinstance(v, (int, float)) and not isinstance(v, bool):
            return -v
        return UNKNOWN
    if isinstance(e, ast.BinaryExpr):
        return _eval_binary(e)
    if isinstance(e, ast.LogicalExpr):
        return _eval_logical(e)
    # 标识符 / 调用 / 下标 / 列表字面量等一律视为动态值
    return UNKNOWN


def _eval_binary(e: ast.BinaryExpr):
    l = const_eval(e.left)
    r = const_eval(e.right)
    op = e.op
    # 相等 / 不等：只要两侧都是字面量常量即可判定（含 null / 类型差异）
    if op == "==":
        if l is UNKNOWN or r is UNKNOWN:
            return UNKNOWN
        if isinstance(l, bool) != isinstance(r, bool):
            return False  # 与 vm._eq 一致：bool 与非 bool 不相等
        return l == r
    if op == "!=":
        if l is UNKNOWN or r is UNKNOWN:
            return UNKNOWN
        if isinstance(l, bool) != isinstance(r, bool):
            return True
        return l != r
    if l is UNKNOWN or r is UNKNOWN:
        return UNKNOWN
    # 字符串拼接
    if op == "+" and (isinstance(l, str) or isinstance(r, str)):
        if isinstance(l, str) and isinstance(r, str):
            return l + r
        return UNKNOWN
    # 算术 / 比较仅对数值常量折叠；除零等会产生运行时错误的情形不折叠
    num = (int, float)
    if isinstance(l, num) and isinstance(r, num) and not isinstance(l, bool) and not isinstance(r, bool):
        try:
            if op == "+":
                return l + r
            if op == "-":
                return l - r
            if op == "*":
                return l * r
            if op == "/" and r != 0:
                return l / r
            if op == "%" and r != 0:
                return l % r
            if op == "<":
                return l < r
            if op == "<=":
                return l <= r
            if op == ">":
                return l > r
            if op == ">=":
                return l >= r
        except (TypeError, ZeroDivisionError, OverflowError):
            return UNKNOWN
    return UNKNOWN


def _eval_logical(e: ast.LogicalExpr):
    l = const_eval(e.left)
    lt = _truthy(l)
    if lt is None:
        return UNKNOWN
    if e.op == "&&":
        if lt is False:
            return l  # 短路，结果为左值
        return const_eval(e.right)
    else:  # ||
        if lt is True:
            return l
        return const_eval(e.right)


# ---------------------------------------------------------------------------
# 节点跨度（结束行）
# ---------------------------------------------------------------------------
def _end_line(node) -> int:
    """保守地求一个 AST 节点占用的最后一行（用于整段高亮）。"""
    if node is None:
        return 0
    if isinstance(node, ast.Block):
        end = node.line
        for s in node.statements:
            end = max(end, _end_line(s))
        return end
    if isinstance(node, ast.IfStmt):
        end = node.line
        for cond, body in node.branches:
            end = max(end, _end_line(cond), _end_line(body))
        if node.else_block:
            end = max(end, _end_line(node.else_block))
        return end
    if isinstance(node, ast.WhileStmt):
        return max(_end_line(node.condition), _end_line(node.body), node.line)
    if isinstance(node, ast.ForStmt):
        end = _end_line(node.body)
        if node.init:
            end = max(end, _end_line(node.init))
        if node.condition:
            end = max(end, _end_line(node.condition))
        if node.increment:
            end = max(end, _end_line(node.increment))
        return max(end, node.line)
    if isinstance(node, ast.VarDecl):
        return _end_line(node.initializer) if node.initializer else node.line
    if isinstance(node, ast.AssignStmt):
        return max(_end_line(node.target), _end_line(node.value))
    if isinstance(node, ast.ExprStmt):
        return _end_line(node.expr)
    if isinstance(node, ast.PrintStmt):
        end = node.line
        for a in node.args:
            end = max(end, _end_line(a))
        return end
    if isinstance(node, ast.ReturnStmt):
        return _end_line(node.value) if node.value else node.line
    if isinstance(node, (ast.BreakStmt, ast.ContinueStmt)):
        return node.line
    if isinstance(node, ast.FunctionDecl):
        return _end_line(node.body)
    # 表达式节点
    end = getattr(node, "line", 1)
    for attr in ("operand", "left", "right", "target", "index", "callee"):
        child = getattr(node, attr, None)
        if child is not None and hasattr(child, "line"):
            end = max(end, _end_line(child))
    for attr in ("args", "elements"):
        children = getattr(node, attr, None)
        if children:
            for c in children:
                end = max(end, _end_line(c))
    return end


# ---------------------------------------------------------------------------
# 原因 -> 文案
# ---------------------------------------------------------------------------
def _message(reason: str) -> str:
    return {
        "after_return": "此处的语句永远无法执行：前面的 return 已无条件退出当前函数",
        "after_break": "此处的语句永远无法执行：前面的 break 已无条件跳出循环",
        "after_continue": "此处的语句永远无法执行：前面的 continue 已无条件进入下一轮循环",
        "false_branch": "此分支永远无法执行：条件恒为 false",
        "else_after_true": "else 分支永远无法执行：前置条件恒为 true",
        "false_loop": "循环体永远无法执行：循环条件恒为 false",
        "infinite_loop": "此处的语句永远无法执行：前面的循环没有 break 且条件恒为 true，永远不会结束",
    }.get(reason, "此段代码永远无法执行")


# ---------------------------------------------------------------------------
# 可达性分析器
# ---------------------------------------------------------------------------
class DeadCodeAnalyzer:
    def __init__(self):
        self.diagnostics = DiagnosticBag()
        self.regions: List[DeadRegion] = []
        self.source_lines: List[str] = []

    def set_source(self, source: str):
        self.source_lines = source.split("\n")

    def analyze(self, program: ast.Program):
        # 顶层声明放在同一条序列里分析：顶层 return 之后的语句不可达，
        # 函数声明由序列逻辑单独进入函数体分析（每个函数体是独立的控制流）。
        self._sequence(list(program.declarations))
        return self

    # ------------------------------------------------------------------
    # 语句序列：在其上顺序传播可达性
    # ------------------------------------------------------------------
    def _sequence(self, stmts: List[ast.Stmt]) -> int:
        """分析一条语句序列，返回该序列可能的出口位掩码。"""
        exits = NORMAL  # 空序列：正常落到序列之后
        # 当前正在累积的不可达区域：[首个语句, 最后语句, 原因]
        pending: Optional[List] = None

        for s in stmts:
            if exits & NORMAL:
                # 进入新的可达语句前，先结算上一段不可达区域
                self._flush(pending)
                pending = None
                stmt_exits = self._stmt(s)
                # 顺序复合：旧路径里只有 NORMAL 能进入本语句，其余出口与
                # 本语句的出口并列成为整个序列的出口。
                exits = (exits & ~NORMAL) | stmt_exits
            else:
                # 当前语句不可达：确定导致不可达的原因
                reason = self._blocked_reason(exits)
                if isinstance(s, ast.FunctionDecl):
                    # 嵌套函数声明会被提升、本身不生成可执行指令；
                    # 关闭当前区域，函数体仍独立分析。
                    self._flush(pending)
                    pending = None
                    self._sequence(s.body.statements)
                    continue
                if pending is None:
                    pending = [s, s, reason]
                else:
                    pending[1] = s
                # 不递归进入不可达语句，其整段都会被高亮

        self._flush(pending)
        return exits

    @staticmethod
    def _blocked_reason(exits: int) -> str:
        if exits & RETURN:
            return "after_return"
        if exits & INFINITE:
            return "infinite_loop"
        if exits & BREAK:
            return "after_break"
        return "after_continue"

    def _flush(self, pending):
        if pending is None:
            return
        first, last, reason = pending
        end = max(_end_line(last), first.line)
        self._report(first.line, end, reason)

    def _report(self, start_line: int, end_line: int, reason: str):
        end_line = max(end_line, start_line)
        message = _message(reason)
        self.regions.append(DeadRegion(start_line, end_line, reason, message))
        col, length = self._span(start_line)
        self.diagnostics.add(Diagnostic(
            SEVERITY_WARNING, PHASE_DEADCODE, KIND_SYNTAX,
            message, start_line, col, length, end_line, col + length,
            "删除这段永远不会执行的代码，或修正前面的控制流 / 条件。",
            None, self._source_line(start_line)))

    def _span(self, line: int) -> Tuple[int, int]:
        """诊断高亮跨度：指向该行首个非空白字符。"""
        idx = line - 1
        if 0 <= idx < len(self.source_lines):
            text = self.source_lines[idx]
            stripped = text.lstrip()
            if stripped:
                col = len(text) - len(stripped) + 1
                return col, max(1, len(stripped.split()[0]))
        return 1, 1

    def _source_line(self, line: int) -> str:
        idx = line - 1
        if 0 <= idx < len(self.source_lines):
            return self.source_lines[idx]
        return ""

    # ------------------------------------------------------------------
    # 单语句：返回从该语句出发可能的出口位掩码
    # ------------------------------------------------------------------
    def _stmt(self, s: ast.Stmt) -> int:
        if s is None:
            return NORMAL
        if isinstance(s, ast.Block):
            return self._sequence(s.statements)
        if isinstance(s, ast.ReturnStmt):
            return RETURN
        if isinstance(s, ast.BreakStmt):
            return BREAK
        if isinstance(s, ast.ContinueStmt):
            return CONTINUE
        if isinstance(s, ast.IfStmt):
            return self._if(s)
        if isinstance(s, ast.WhileStmt):
            return self._while(s)
        if isinstance(s, ast.ForStmt):
            return self._for(s)
        if isinstance(s, ast.FunctionDecl):
            # 嵌套函数：函数体独立分析；声明处不影响外层控制流
            self._sequence(s.body.statements)
            return NORMAL
        # VarDecl / AssignStmt / ExprStmt / PrintStmt
        return NORMAL

    # ------------------------------------------------------------------
    # if / elif / else
    # ------------------------------------------------------------------
    def _if(self, s: ast.IfStmt) -> int:
        exits = 0
        may_skip = False        # 是否存在"所有分支都不进、落到 if 之后"的路径
        taken_true = False      # 是否已有恒真分支（其后的 elif/else 均不可达）
        dead_tail: List[Tuple[ast.Block, str]] = []  # 恒真/恒假分支块

        for cond, body in s.branches:
            tv = static_truth(cond)
            if taken_true or tv is False:
                dead_tail.append((body, "false_branch"))
                continue
            exits |= self._sequence(body.statements)
            if tv is True:
                taken_true = True
            else:
                may_skip = True  # 条件未知：该分支可能不进入

        if s.else_block is not None:
            if taken_true:
                dead_tail.append((s.else_block, "else_after_true"))
            else:
                # 有 else 时不可能"绕过整个 if"：未知条件下必进 else 或某个分支
                may_skip = False
                exits |= self._sequence(s.else_block.statements)
        elif not taken_true:
            # 没有 else：存在未知条件或全为恒假时，控制流可绕过整个 if
            may_skip = True

        if may_skip:
            exits |= NORMAL
        for body, reason in dead_tail:
            self._report_block(body, reason)
        return exits

    def _report_block(self, block: ast.Block, reason: str):
        """把一个整块标记为不可达（空块不产生诊断）。"""
        first = self._first_stmt(block)
        if first is None:
            return
        self._report(first.line, _end_line(block), reason)

    @staticmethod
    def _first_stmt(block: ast.Block):
        for s in block.statements:
            if isinstance(s, ast.FunctionDecl):
                continue
            return s
        return None

    # ------------------------------------------------------------------
    # while
    # ------------------------------------------------------------------
    def _while(self, s: ast.WhileStmt) -> int:
        tv = static_truth(s.condition)
        if tv is False:
            # 循环体一次也不会执行
            self._report_block(s.body, "false_loop")
            return NORMAL

        body_exits = self._sequence(s.body.statements)
        # NORMAL：体正常跑完一轮 -> 回到条件处，不是循环出口；
        # CONTINUE：显式回到条件处，同样不是循环出口。
        body_exits &= ~(NORMAL | CONTINUE)

        if tv is True:
            # 恒真循环：break 离开 => NORMAL；return 离开 => RETURN；
            # 两者都没有 => 循环永不结束（INFINITE）。
            exits = 0
            if body_exits & RETURN:
                exits |= RETURN
            if body_exits & BREAK:
                exits |= NORMAL
            return exits if exits else INFINITE

        # 条件未知：条件为假时直接退出（NORMAL）；break 也转为 NORMAL。
        exits = NORMAL
        if body_exits & RETURN:
            exits |= RETURN
        return exits

    # ------------------------------------------------------------------
    # for
    # ------------------------------------------------------------------
    def _for(self, s: ast.ForStmt) -> int:
        if s.init:
            self._stmt(s.init)

        cond_tv = True  # 无条件时等价于恒真
        if s.condition is not None:
            cond_tv = static_truth(s.condition)

        if cond_tv is False:
            # 循环体与 increment 都不可达
            self._report_for_body(s)
            return NORMAL

        body_exits = self._sequence(s.body.statements)
        # NORMAL：体正常跑完一轮 -> 执行 increment 后回到条件处；
        # CONTINUE：显式回到条件处。两者都不是 for 的直接出口。
        body_exits &= ~(NORMAL | CONTINUE)
        # increment 在"正常跑完一轮 / continue"时执行；这里保守视为可达，
        # 表达式本身不含语句，不会产生新的死代码区域。
        # （不做更激进的判定，避免把与循环体同行书写的 increment 误标。）

        if cond_tv is True:
            # 恒真 for：break 离开 => NORMAL；return 离开 => RETURN；
            # 两者都没有 => 循环永不结束（INFINITE）。
            exits = 0
            if body_exits & RETURN:
                exits |= RETURN
            if body_exits & BREAK:
                exits |= NORMAL
            return exits if exits else INFINITE

        # 条件未知：条件为假时退出；break 转为正常出口
        exits = NORMAL
        if body_exits & RETURN:
            exits |= RETURN
        return exits

    def _report_for_body(self, s: ast.ForStmt):
        """恒假 for 循环：循环体整段不可达。

        空循环体不产生诊断——increment 与 for 头同行书写，而 init 仍然执行，
        高亮整行会产生误导。
        """
        first = self._first_stmt(s.body)
        if first is None:
            return
        self._report(first.line, _end_line(s.body), "false_loop")


# ---------------------------------------------------------------------------
# 便捷入口
# ---------------------------------------------------------------------------
def analyze_dead_code(program: ast.Program, source: str = ""):
    """对 Program 做死代码检测，返回 DeadCodeAnalyzer。"""
    analyzer = DeadCodeAnalyzer()
    analyzer.set_source(source)
    analyzer.analyze(program)
    return analyzer
