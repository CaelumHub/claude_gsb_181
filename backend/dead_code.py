# -*- coding: utf-8 -*-
"""
死代码分析（不可达语句检测）。

该遍在语法树和语义分析之后运行，用保守的路径敏感规则模拟语句执行后的
控制流，只报告能够由语法与常量真值确定的不可达代码：

* ``return`` / ``break`` / ``continue`` 等终止语句之后顺序执行的语句；
* 恒假 ``if/elif/while`` 分支或循环体；
* 恒真条件之后不可达的 ``elif/else``；
* 没有 break/return 等出口的无限循环之后的语句；
* 恒假 ``for`` 条件下不会执行的循环体与增量表达式。

为避免误报，函数调用、标识符、下标、可能抛运行时异常的表达式均视为
静态未知；未知条件的分支一律按“可能执行”处理。函数体相互独立分析，
顶层函数声明按语言现有“函数提升”语义处理。
"""

from dataclasses import dataclass
from typing import List, Optional

from . import ast_nodes as ast
from .diagnostics import DiagnosticBag, warning_dead_code


UNKNOWN = object()


@dataclass
class Flow:
    """一段语句执行结束后，控制流可能到达的位置。"""
    normal: bool = False       # 可以顺序流入下一条语句
    return_out: bool = False   # 可能从当前函数返回
    break_out: bool = False    # 可能跳出当前循环
    continue_out: bool = False # 可能跳到当前循环的增量/下一次判断

    @property
    def reachable_next(self) -> bool:
        return self.normal

    @classmethod
    def normal_flow(cls) -> "Flow":
        return cls(normal=True)

    @classmethod
    def terminated(cls, *, return_out=False, break_out=False, continue_out=False) -> "Flow":
        return cls(False, return_out, break_out, continue_out)

    @classmethod
    def join(cls, flows: List["Flow"]) -> "Flow":
        return cls(
            normal=any(f.normal for f in flows),
            return_out=any(f.return_out for f in flows),
            break_out=any(f.break_out for f in flows),
            continue_out=any(f.continue_out for f in flows),
        )


def _sequence_flow(first: Flow, second: Flow) -> Flow:
    """合并顺序执行的两段控制流。"""
    return Flow(
        normal=first.normal and second.normal,
        return_out=first.return_out or (first.normal and second.return_out),
        break_out=first.break_out or (first.normal and second.break_out),
        continue_out=first.continue_out or (first.normal and second.continue_out),
    )


class DeadCodeAnalyzer:
    def __init__(self, source: str):
        self.source = source
        self.source_lines = source.split("\n")
        self.diagnostics = DiagnosticBag()
        self._spans = set()
        line_start = 0
        self.line_starts = []
        for line in self.source_lines:
            self.line_starts.append(line_start)
            line_start += len(line) + 1

    # ------------------------------------------------------------------
    # 入口
    # ------------------------------------------------------------------
    def analyze(self, program: ast.Program) -> DiagnosticBag:
        flow = Flow.normal_flow()
        for decl in program.declarations:
            if isinstance(decl, ast.FunctionDecl):
                # 顶层函数由代码生成阶段预先注册，文本位置不代表调用路径。
                self._analyze_function(decl)
                continue
            if not flow.reachable_next:
                self._mark(decl, "unreachable")
                continue
            cur = self._stmt(decl)
            flow = _sequence_flow(flow, cur)
        return self.diagnostics

    def _analyze_function(self, fn: ast.FunctionDecl):
        self._analyze_block(fn.body)

    # ------------------------------------------------------------------
    # 语句控制流
    # ------------------------------------------------------------------
    def _analyze_block(self, block: ast.Block) -> Flow:
        flow = Flow.normal_flow()
        for stmt in block.statements:
            if isinstance(stmt, ast.FunctionDecl):
                # 嵌套函数体是独立的作用域与调用路径；声明本身不终止当前流程。
                self._analyze_function(stmt)
                continue
            if not flow.reachable_next:
                self._mark(stmt, "unreachable")
                continue
            cur = self._stmt(stmt)
            flow = _sequence_flow(flow, cur)
        return flow

    def _stmt(self, stmt: ast.Stmt) -> Flow:
        if isinstance(stmt, ast.Block):
            return self._analyze_block(stmt)
        if isinstance(stmt, (ast.VarDecl, ast.AssignStmt, ast.ExprStmt, ast.PrintStmt)):
            return Flow.normal_flow()
        if isinstance(stmt, ast.ReturnStmt):
            return Flow.terminated(return_out=True)
        if isinstance(stmt, ast.BreakStmt):
            return Flow.terminated(break_out=True)
        if isinstance(stmt, ast.ContinueStmt):
            return Flow.terminated(continue_out=True)
        if isinstance(stmt, ast.IfStmt):
            return self._if_stmt(stmt)
        if isinstance(stmt, ast.WhileStmt):
            return self._while_stmt(stmt)
        if isinstance(stmt, ast.ForStmt):
            return self._for_stmt(stmt)
        # 未知语句保守地认为可以继续，避免误报。
        return Flow.normal_flow()

    def _if_stmt(self, stmt: ast.IfStmt) -> Flow:
        """逐条分析 if-elif-else 链；taken 表示前面是否已有恒真分支。"""
        flows = []
        branch_taken = False

        for cond, body in stmt.branches:
            value = self._const_truth(cond)
            if branch_taken or value is False:
                reason = "else_after_true" if branch_taken else "false_branch"
                self._mark(body, reason)
                continue

            body_flow = self._analyze_block(body)
            flows.append(body_flow)
            if value is True:
                branch_taken = True

        if stmt.else_block is not None:
            if branch_taken:
                self._mark(stmt.else_block, "else_after_true")
            else:
                flows.append(self._analyze_block(stmt.else_block))
        else:
            # 没有 else 时，所有前面的条件都可能同时为假，因此存在落空路径。
            if not branch_taken:
                flows.append(Flow.normal_flow())

        return Flow.join(flows)

    def _while_stmt(self, stmt: ast.WhileStmt) -> Flow:
        value = self._const_truth(stmt.condition)
        if value is False:
            self._mark(stmt.body, "false_loop")
            return Flow.normal_flow()

        body = self._analyze_block(stmt.body)
        if value is True:
            return Flow(
                normal=body.break_out,
                return_out=body.return_out,
                break_out=False,
                continue_out=False,
            )

        # 条件未知：条件为假时可退出；break 只影响本循环，不向外传播。
        return Flow(normal=True, return_out=body.return_out)

    def _for_stmt(self, stmt: ast.ForStmt) -> Flow:
        if stmt.init is not None:
            self._stmt(stmt.init)

        value = self._const_truth(stmt.condition) if stmt.condition is not None else True
        if value is False:
            self._mark(stmt.body, "false_loop")
            if stmt.increment is not None:
                self._mark_for_increment(stmt.increment, "false_loop")
            return Flow.normal_flow()

        body = self._analyze_block(stmt.body)
        increment_reachable = body.normal or body.continue_out or body.break_out
        if stmt.increment is not None and not increment_reachable:
            self._mark_for_increment(stmt.increment, "unreachable")

        if value is True:
            return Flow(
                normal=body.break_out,
                return_out=body.return_out,
                break_out=False,
                continue_out=False,
            )
        return Flow(normal=True, return_out=body.return_out)

    # ------------------------------------------------------------------
    # 保守常量表达式求值
    # ------------------------------------------------------------------
    def _const_value(self, expr):
        if isinstance(expr, ast.BoolLiteral):
            return expr.value
        if isinstance(expr, ast.NullLiteral):
            return None
        if isinstance(expr, ast.NumberLiteral):
            return expr.value
        if isinstance(expr, ast.StringLiteral):
            # 词法通常会保留外层引号；兼容已去掉引号的空串。
            text = expr.value
            return text[1:-1] if len(text) >= 2 and text[0] == '"' and text[-1] == '"' else text
        if isinstance(expr, ast.UnaryExpr):
            v = self._const_value(expr.operand)
            if v is UNKNOWN:
                return UNKNOWN
            if expr.op == "!":
                return not self._truthy(v)
            if expr.op == "-" and self._is_number(v):
                return -v
            return UNKNOWN
        if isinstance(expr, ast.LogicalExpr):
            left = self._const_value(expr.left)
            if left is UNKNOWN:
                return UNKNOWN
            if expr.op == "&&":
                return left if not self._truthy(left) else self._const_value(expr.right)
            if expr.op == "||":
                return left if self._truthy(left) else self._const_value(expr.right)
            return UNKNOWN
        if isinstance(expr, ast.BinaryExpr):
            return self._const_binary(expr)
        # 标识符、函数调用、下标、列表等均可能受运行状态影响，按未知处理。
        return UNKNOWN

    def _const_truth(self, expr):
        value = self._const_value(expr)
        if value is UNKNOWN:
            return UNKNOWN
        return self._truthy(value)

    def _const_binary(self, expr: ast.BinaryExpr):
        left = self._const_value(expr.left)
        right = self._const_value(expr.right)
        if left is UNKNOWN or right is UNKNOWN:
            return UNKNOWN
        op = expr.op
        try:
            if op == "+":
                if self._is_number(left) and self._is_number(right):
                    return left + right
                if isinstance(left, str) and isinstance(right, str):
                    return left + right
                return UNKNOWN
            if op in ("-", "*", "/", "%"):
                if not (self._is_number(left) and self._is_number(right)):
                    return UNKNOWN
                if op == "-":
                    return left - right
                if op == "*":
                    return left * right
                if right == 0:
                    return UNKNOWN
                return left / right if op == "/" else left % right
            if op in ("==", "!="):
                result = self._const_equal(left, right)
                return result if op == "==" else not result
            # bool 不是数字类型；不匹配的比较在 MiniLang 中是运行时错误，不能用于判定分支。
            if not self._orderable(left, right):
                return UNKNOWN
            if op in ("<", "<=", ">", ">="):
                if op == "<": return left < right
                if op == "<=": return left <= right
                if op == ">": return left > right
                return left >= right
        except (TypeError, ValueError, ArithmeticError):
            return UNKNOWN
        return UNKNOWN

    @staticmethod
    def _truthy(value) -> bool:
        return value is not None and value is not False

    @staticmethod
    def _is_number(value) -> bool:
        return isinstance(value, (int, float)) and not isinstance(value, bool)

    @staticmethod
    def _orderable(left, right) -> bool:
        if DeadCodeAnalyzer._is_number(left) and DeadCodeAnalyzer._is_number(right):
            return True
        return isinstance(left, str) and isinstance(right, str)

    @staticmethod
    def _const_equal(left, right) -> bool:
        if left is None or right is None:
            return left is None and right is None
        if isinstance(left, bool) != isinstance(right, bool):
            return False
        return left == right

    # ------------------------------------------------------------------
    # 源码范围定位
    # ------------------------------------------------------------------
    def _mark_for_increment(self, node, reason: str):
        start = self._offset(node.line, node.column)
        if start is None:
            return
        end = self._find_terminator(start, ";", extra=")")
        line_end = self._line_end(node.line)
        end = end if end is not None and end <= line_end else line_end
        self._mark_span(start, end, reason)

    def _mark(self, node, reason: str):
        span = self._span(node)
        if span is None:
            return
        self._mark_span(span[0], span[1], reason)

    def _mark_span(self, start_offset: int, end_offset: int, reason: str):
        if start_offset >= end_offset or (start_offset, end_offset) in self._spans:
            return
        self._spans.add((start_offset, end_offset))
        start_line, start_col = self._line_col(start_offset)
        end_line, end_col = self._line_col(end_offset)
        source_line = self.source_lines[start_line - 1] if start_line <= len(self.source_lines) else ""
        self.diagnostics.add(warning_dead_code(
            reason, start_line, start_col, end_line, end_col, source_line,
            start_offset, end_offset))

    def _span(self, node) -> Optional[tuple]:
        if node is None or not hasattr(node, "line"):
            return None
        start = self._offset(node.line, node.column)
        if start is None or start >= len(self.source):
            return None

        if isinstance(node, ast.FunctionDecl):
            brace = self._find_curly_open(start)
            return (start, brace if brace is not None else self._line_end(node.line))
        if isinstance(node, ast.Block):
            end = self._find_matching_curly(start)
            return (start, end if end is not None else self._line_end(node.line))
        if isinstance(node, (ast.IfStmt, ast.WhileStmt, ast.ForStmt)):
            end = self._find_statement_curly_end(start)
            return (start, end if end is not None else self._line_end(node.line))
        if isinstance(node, (ast.ReturnStmt, ast.BreakStmt, ast.ContinueStmt,
                             ast.VarDecl, ast.AssignStmt, ast.ExprStmt, ast.PrintStmt)):
            semi = self._find_terminator(start, ";")
            line_end = self._line_end(node.line)
            return (start, semi if semi is not None and semi <= line_end else line_end)

        # 目前用于 for 增量表达式：停在同级的 ; 或 for 头的右括号。
        end = self._find_terminator(start, ";", extra=")")
        return (start, end if end is not None else self._line_end(node.line))

    def _offset(self, line: int, column: int) -> Optional[int]:
        if line < 1 or line > len(self.line_starts):
            return None
        return self.line_starts[line - 1] + max(0, column - 1)

    def _line_end(self, line: int) -> int:
        if line < 1 or line > len(self.source_lines):
            return len(self.source)
        return self.line_starts[line - 1] + len(self.source_lines[line - 1])

    def _line_col(self, offset: int) -> tuple:
        line = 1
        for i, start in enumerate(self.line_starts, start=1):
            if start <= offset:
                line = i
            else:
                break
        return line, offset - self.line_starts[line - 1] + 1

    def _skip_noise(self, i: int) -> int:
        """跳过字符串与注释，返回下一个普通字符位置。"""
        n = len(self.source)
        if i >= n:
            return i
        ch = self.source[i]
        if ch == '"':
            j = i + 1
            while j < n:
                if self.source[j] == "\\":
                    j += 2
                    continue
                if self.source[j] in ('"', "\n"):
                    return min(j + 1, n)
                j += 1
            return n
        if ch == "/" and i + 1 < n and self.source[i + 1] == "/":
            j = self.source.find("\n", i + 2)
            return n if j == -1 else j + 1
        if ch == "/" and i + 1 < n and self.source[i + 1] == "*":
            end = self.source.find("*/", i + 2)
            return n if end == -1 else min(end + 2, n)
        return i

    def _find_curly_open(self, start: int) -> Optional[int]:
        i = start
        n = len(self.source)
        while i < n:
            i = self._skip_noise(i)
            if i >= n:
                break
            if self.source[i] == "{":
                return i
            if self.source[i] == ";":
                return None
            i += 1
        return None

    def _find_matching_curly(self, open_pos: int) -> Optional[int]:
        if open_pos >= len(self.source) or self.source[open_pos] != "{":
            return None
        depth = 0
        i = open_pos
        n = len(self.source)
        while i < n:
            i = self._skip_noise(i)
            if i >= n:
                break
            ch = self.source[i]
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    return i + 1
            i += 1
        return None

    def _find_statement_curly_end(self, start: int) -> Optional[int]:
        """找到 if/while/for 最外层最后一个代码块的闭合大括号。"""
        i = start
        n = len(self.source)
        depth = 0
        last_end = None
        while i < n:
            i = self._skip_noise(i)
            if i >= n:
                break
            ch = self.source[i]
            if ch == "{":
                depth += 1
            elif ch == "}":
                if depth > 0:
                    depth -= 1
                    if depth == 0:
                        last_end = i + 1
            elif ch == ";" and depth == 0:
                break
            i += 1
        return last_end

    def _find_terminator(self, start: int, target: str, extra: str = "") -> Optional[int]:
        stack = []
        pairs = {")": "(", "]": "[", "}": "{"}
        i = start
        n = len(self.source)
        while i < n:
            i = self._skip_noise(i)
            if i >= n:
                break
            ch = self.source[i]
            if not stack and (ch == target or (extra and ch == extra)):
                return i
            if ch in "([{":
                stack.append(ch)
            elif ch in ")]}":
                if stack and stack[-1] == pairs[ch]:
                    stack.pop()
            elif not stack and ch == "\n" and target == ";":
                # MiniLang 语句显式以分号结束；兼容容错源码时不跨行猜测。
                return None
            i += 1
        return None


def analyze_dead_code(source: str, program: ast.Program) -> DiagnosticBag:
    return DeadCodeAnalyzer(source).analyze(program)
