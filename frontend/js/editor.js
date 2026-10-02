/* ============================================================
   MiniLang 平台 —— 代码编辑器组件
   纯前端实现语法高亮（手写词法着色）+ 自动补全（关键字/内置/变量/函数）。
   同时支持断点槽（点击行号设置断点）与当前执行行高亮，供调试页复用。
   ============================================================ */
(function () {
  "use strict";

  const ML = (window.ML = window.ML || {});

  const KEYWORDS = new Set(["var", "func", "if", "elif", "else", "while", "for",
    "return", "break", "continue", "print", "true", "false", "null"]);
  const BUILTINS = new Set(["print", "len", "push", "pop", "type", "str", "int",
    "float", "range", "abs", "min", "max", "sqrt", "floor", "ceil", "round",
    "input", "exit", "time", "random"]);

  const DOUBLE_OPS = ["==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%="];
  const SINGLE_OPS = "+-*/%!=<>(){}[],;.";

  /* ----------------------------------------------------------
   * 词法着色：把 MiniLang 源码转成带高亮的 HTML
   * ---------------------------------------------------------- */
  ML.Highlighter = {
    highlight(code) {
      const esc = ML.escapeHtml;
      let out = "";
      let i = 0;
      const n = code.length;
      while (i < n) {
        const ch = code[i];
        // 行注释
        if (ch === "/" && code[i + 1] === "/") {
          let j = i;
          while (j < n && code[j] !== "\n") j++;
          out += '<span class="tk-com">' + esc(code.slice(i, j)) + "</span>";
          i = j;
          continue;
        }
        // 块注释
        if (ch === "/" && code[i + 1] === "*") {
          let j = code.indexOf("*/", i + 2);
          j = j === -1 ? n : j + 2;
          out += '<span class="tk-com">' + esc(code.slice(i, j)) + "</span>";
          i = j;
          continue;
        }
        // 字符串
        if (ch === '"') {
          let j = i + 1;
          while (j < n) {
            if (code[j] === "\\") { j += 2; continue; }
            if (code[j] === '"') { j++; break; }
            if (code[j] === "\n") break;
            j++;
          }
          out += '<span class="tk-str">' + esc(code.slice(i, j)) + "</span>";
          i = j;
          continue;
        }
        // 数字
        if (/[0-9]/.test(ch) || (ch === "." && /[0-9]/.test(code[i + 1] || ""))) {
          const m = code.slice(i).match(/^(\d+\.?\d*(?:[eE][+-]?\d+)?|\.\d+)/);
          if (m) {
            out += '<span class="tk-num">' + esc(m[0]) + "</span>";
            i += m[0].length;
            continue;
          }
        }
        // 标识符 / 关键字 / 内置
        if (/[A-Za-z_]/.test(ch)) {
          let j = i;
          while (j < n && /[A-Za-z0-9_]/.test(code[j])) j++;
          const word = code.slice(i, j);
          let cls = "tk-ident";
          if (KEYWORDS.has(word)) cls = "tk-kw";
          else if (BUILTINS.has(word)) cls = "tk-bi";
          out += '<span class="' + cls + '">' + esc(word) + "</span>";
          i = j;
          continue;
        }
        // 运算符（双字符优先）
        const two = code.slice(i, i + 2);
        if (DOUBLE_OPS.includes(two)) {
          out += '<span class="tk-op">' + esc(two) + "</span>";
          i += 2;
          continue;
        }
        if (SINGLE_OPS.includes(ch)) {
          out += '<span class="tk-op">' + esc(ch) + "</span>";
          i += 1;
          continue;
        }
        out += esc(ch);
        i += 1;
      }
      return out;
    },
  };

  /* ----------------------------------------------------------
   * 从源码中收集已声明的符号（用于补全）
   * ---------------------------------------------------------- */
  function collectSymbols(code) {
    const fns = new Map(); // name -> {kind, params}
    const vars = new Set();
    const params = new Set();
    let m;
    const fnRe = /\bfunc\s+([A-Za-z_]\w*)\s*\(([^)]*)\)/g;
    while ((m = fnRe.exec(code)) !== null) {
      fns.set(m[1], { kind: "函数" });
      m[2].split(",").map((s) => s.trim()).filter(Boolean).forEach((p) => params.add(p));
    }
    const varRe = /\bvar\s+([A-Za-z_]\w*)/g;
    while ((m = varRe.exec(code)) !== null) vars.add(m[1]);
    return { fns, vars, params };
  }

  /* ----------------------------------------------------------
   * CodeEditor 组件
   * ---------------------------------------------------------- */
  ML.CodeEditor = class {
    /**
     * @param {HTMLElement} container 挂载点
     * @param {object} opts
     *   value: 初始源码
     *   height: 最小高度（px，默认 320）
     *   breakpoints: 是否显示断点槽
     *   onBreakpointChange: (line, active) => void
     *   onValueChange: (value) => void
     *   autocomplete: 是否启用自动补全（默认 true）
     */
    constructor(container, opts) {
      opts = opts || {};
      this.container = container;
      this.breakpointsEnabled = !!opts.breakpoints;
      this.onBreakpointChange = opts.onBreakpointChange || null;
      this.onValueChange = opts.onValueChange || null;
      this.autocomplete = opts.autocomplete !== false;
      this._bps = new Set();
      this._tabSize = 4;
      this._charW = null;
      this._acBox = null;
      this._acSel = 0;
      this._acItems = [];
      this._deadMarkers = [];
      this._deadLines = new Set();
      this._deadSource = "";
      this._buildDom(opts);
    }

    _buildDom(opts) {
      const wrap = document.createElement("div");
      wrap.className = "editor-wrap";
      wrap.style.minHeight = (opts.height || 320) + "px";

      this.gutterInner = document.createElement("div");
      this.gutterInner.className = "gutter-inner";
      const gutter = document.createElement("div");
      gutter.className = "gutter";
      gutter.appendChild(this.gutterInner);

      this.hlInner = document.createElement("span");
      this.hlInner.className = "hl-inner";
      this.hl = document.createElement("pre");
      this.hl.className = "hl";
      this.hl.setAttribute("aria-hidden", "true");
      this.hl.appendChild(this.hlInner);

      this.deadLayer = document.createElement("div");
      this.deadLayer.className = "dead-layer";
      this.deadLayer.setAttribute("aria-hidden", "true");

      this.curLine = document.createElement("div");
      this.curLine.className = "cur-line";
      this.curLine.style.display = "none";

      this.ta = document.createElement("textarea");
      this.ta.className = "src";
      this.ta.spellcheck = false;
      this.ta.wrap = "off";
      this.ta.setAttribute("autocapitalize", "off");
      this.ta.setAttribute("autocorrect", "off");

      const area = document.createElement("div");
      area.className = "code-area";
      area.appendChild(this.hl);
      area.appendChild(this.deadLayer);
      area.appendChild(this.curLine);
      area.appendChild(this.ta);

      wrap.appendChild(gutter);
      wrap.appendChild(area);
      this.container.appendChild(wrap);
      this.wrap = wrap;

      this._bindEvents();
      this.setValue(opts.value != null ? opts.value : "");
    }

    _bindEvents() {
      this.ta.addEventListener("input", () => {
        this.clearDeadCode();
        this._render();
        if (this.onValueChange) this.onValueChange(this.getValue());
      });
      this.ta.addEventListener("scroll", () => this._syncScroll());
      this.ta.addEventListener("keydown", (e) => this._onKeydown(e));
      this.ta.addEventListener("click", () => this._closeAC());
      this.ta.addEventListener("blur", () => setTimeout(() => this._closeAC(), 150));

      if (this.breakpointsEnabled) {
        this.gutterInner.addEventListener("click", (e) => {
          const line = e.target.closest(".gline");
          if (line) this.toggleBreakpoint(parseInt(line.dataset.line, 10));
        });
      }
    }

    /* ---------------- 取值 / 设值 ---------------- */
    getValue() { return this.ta.value; }

    setValue(code) {
      this.ta.value = code;
      this.clearDeadCode();
      this._render();
    }

    setDeadCode(markers, source) {
      if (source != null && source !== this.getValue()) return;
      this._deadSource = source != null ? source : this.getValue();
      this._deadMarkers = (markers || []).filter((m) =>
        m && m.start_offset >= 0 && m.end_offset > m.start_offset &&
        m.end_offset <= this._deadSource.length);
      this._deadLines = new Set();
      this._deadMarkers.forEach((m) => {
        let p = m.start_offset;
        while (p < m.end_offset) {
          const nl = this._deadSource.indexOf("\n", p);
          const lineEnd = nl === -1 || nl >= m.end_offset ? m.end_offset : nl;
          if (lineEnd > p || nl === p) this._deadLines.add(this._offsetToLine(p));
          if (nl === -1 || nl >= m.end_offset) break;
          p = nl + 1;
        }
      });
      this._renderGutter();
      this._renderDeadCode();
      this._syncScroll();
    }

    clearDeadCode() {
      if (!this._deadMarkers.length && !this._deadLines.size) return;
      this._deadMarkers = [];
      this._deadLines = new Set();
      this._deadSource = "";
      this.deadLayer.innerHTML = "";
    }

    getBreakpoints() { return Array.from(this._bps).sort((a, b) => a - b); }

    setBreakpoints(lines) {
      this._bps = new Set(lines || []);
      this._renderGutter();
    }

    toggleBreakpoint(line) {
      if (line < 1) return;
      if (this._bps.has(line)) this._bps.delete(line);
      else this._bps.add(line);
      this._renderGutter();
      if (this.onBreakpointChange) this.onBreakpointChange(line, this._bps.has(line));
      return this._bps.has(line);
    }

    setCurrentLine(line) {
      if (!line) { this.curLine.style.display = "none"; return; }
      this.curLine.style.display = "block";
      this._placeCurLine(line);
    }

    focus() { this.ta.focus(); }

    /* ---------------- 渲染 ---------------- */
    _render() {
      this.hlInner.innerHTML = ML.Highlighter.highlight(this.ta.value) || "​";
      this._renderGutter();
      this._syncScroll();
    }

    _renderGutter() {
      const lines = this.ta.value.split("\n").length;
      let html = "";
      for (let i = 1; i <= lines; i++) {
        const hasBp = this._bps.has(i);
        const isDead = this._deadLines.has(i);
        html += `<div class="gline${hasBp ? " has-bp" : ""}${isDead ? " has-dead" : ""}" data-line="${i}">` +
          `<span class="bp"></span><span class="num">${i}</span></div>`;
      }
      this.gutterInner.innerHTML = html;
    }

    _syncScroll() {
      const st = this.ta.scrollTop, sl = this.ta.scrollLeft;
      this.hlInner.style.transform = `translate(${-sl}px, ${-st}px)`;
      this.deadLayer.style.transform = `translate(${-sl}px, ${-st}px)`;
      this.gutterInner.style.transform = `translateY(${-st}px)`;
      const cur = parseInt(this.ta.dataset.curLine || "0", 10);
      if (cur) this._placeCurLine(cur);
    }

    _placeCurLine(line) {
      const st = this.ta.scrollTop;
      this.curLine.style.top = (12 + (line - 1) * 20 - st) + "px";
    }

    /* ---------------- 死代码高亮 ---------------- */
    _offsetToLine(offset) {
      return this._deadSource.slice(0, offset).split("\n").length;
    }

    _visualCol(lineText, index) {
      let col = 0;
      for (let i = 0; i < index && i < lineText.length; i++) {
        col += lineText[i] === "\t" ? (this._tabSize - (col % this._tabSize)) : 1;
      }
      return col;
    }

    _renderDeadCode() {
      const text = this._deadSource;
      const lines = text.split("\n");
      const lineStarts = [];
      let p = 0;
      for (const line of lines) {
        lineStarts.push(p);
        p += line.length + 1;
      }
      const html = this._deadMarkers.map((m) => {
        const title = ML.escapeHtml(m.message || "永远无法执行到的语句");
        const segments = [];
        const startLine = this._offsetToLine(m.start_offset) - 1;
        const endLine = this._offsetToLine(Math.max(m.start_offset, m.end_offset - 1)) - 1;
        for (let line = startLine; line <= endLine; line++) {
          const lineStart = lineStarts[line];
          const segStart = Math.max(m.start_offset, lineStart);
          const nl = text.indexOf("\n", lineStart);
          const lineEnd = nl === -1 ? text.length : nl;
          const segEnd = Math.min(m.end_offset, lineEnd);
          if (segEnd <= segStart) continue;
          const startIndex = segStart - lineStart;
          const endIndex = segEnd - lineStart;
          const startVisual = this._visualCol(lines[line], startIndex);
          const endVisual = this._visualCol(lines[line], endIndex);
          const width = Math.max(6, (endVisual - startVisual) * this._charWidth());
          segments.push(`<div class="dead-range" title="${title}" style="left:${14 + startVisual * this._charWidth()}px;top:${12 + line * 20}px;width:${width}px"></div>`);
        }
        return segments.join("");
      }).join("");
      this.deadLayer.innerHTML = html;
    }

    /* ---------------- 键盘 / 补全 ---------------- */
    _onKeydown(e) {
      if (this._acBox && ["ArrowDown", "ArrowUp", "Enter", "Tab", "Escape"].includes(e.key)) {
        if (e.key === "ArrowDown") { e.preventDefault(); this._moveAC(1); return; }
        if (e.key === "ArrowUp") { e.preventDefault(); this._moveAC(-1); return; }
        if (e.key === "Enter" || e.key === "Tab") { e.preventDefault(); this._commitAC(); return; }
        if (e.key === "Escape") { e.preventDefault(); this._closeAC(); return; }
      }
      if (e.key === "Tab") {
        e.preventDefault();
        this._insertText(" ".repeat(this._tabSize));
        return;
      }
      if (e.key === "Enter") {
        // 缩进延续
        const { line } = this._cursor();
        const text = this.ta.value;
        const lines = text.split("\n");
        const cur = lines[line] || "";
        const indent = (cur.match(/^[ \t]*/) || [""])[0];
        e.preventDefault();
        this._insertText("\n" + indent);
        return;
      }
      if (e.key === " " && e.ctrlKey) {
        e.preventDefault();
        this._showAC(true);
        return;
      }
      if (e.key.length === 1 && /[A-Za-z_]/.test(e.key)) {
        setTimeout(() => this._showAC(false), 0);
      }
    }

    _cursor() {
      const pos = this.ta.selectionStart;
      const before = this.ta.value.slice(0, pos);
      const lines = before.split("\n");
      return { line: lines.length - 1, col: lines[lines.length - 1].length, pos };
    }

    _currentWord() {
      const { pos, col } = this._cursor();
      const text = this.ta.value;
      let start = pos;
      while (start > 0 && /[A-Za-z0-9_]/.test(text[start - 1])) start--;
      return text.slice(start, pos);
    }

    _insertText(s) {
      const start = this.ta.selectionStart, end = this.ta.selectionEnd;
      this.ta.setRangeText(s, start, end, "end");
      this.clearDeadCode();
      this._render();
      if (this.onValueChange) this.onValueChange(this.getValue());
    }

    _commitAC() {
      const item = this._acItems[this._acSel];
      this._closeAC();
      if (!item) return;
      const word = this._currentWord();
      const { pos } = this._cursor();
      const start = pos - word.length;
      this.ta.setRangeText(item.text, start, pos, "end");
      this._render();
      if (this.onValueChange) this.onValueChange(this.getValue());
    }

    _buildItems(force) {
      const word = this._currentWord();
      if (!force && word.length === 0) return [];
      const sym = collectSymbols(this.ta.value);
      const items = [];
      const add = (text, kind) => items.push({ text, kind });
      KEYWORDS.forEach((k) => add(k, "关键字"));
      BUILTINS.forEach((b) => add(b, "内置函数"));
      sym.fns.forEach((_, name) => add(name, "函数"));
      sym.params.forEach((p) => add(p, "形参"));
      sym.vars.forEach((v) => add(v, "变量"));
      const seen = new Set();
      const uniq = items.filter((it) => {
        if (seen.has(it.text)) return false;
        seen.add(it.text);
        if (word && !it.text.startsWith(word)) return false;
        return true;
      });
      return uniq.slice(0, 40);
    }

    _showAC(force) {
      if (!this.autocomplete) return;
      const items = this._buildItems(force);
      if (!items.length) { this._closeAC(); return; }
      this._acItems = items;
      this._acSel = 0;
      this._renderAC();
    }

    _renderAC() {
      if (!this._acBox) {
        this._acBox = document.createElement("div");
        this._acBox.className = "ac-box";
        this.wrap.appendChild(this._acBox);
      }
      let html = "";
      this._acItems.forEach((it, idx) => {
        html += `<div class="item${idx === this._acSel ? " sel" : ""}" data-i="${idx}">` +
          `<span class="t">${ML.escapeHtml(it.text)}</span>` +
          `<span class="k">${ML.escapeHtml(it.kind)}</span></div>`;
      });
      this._acBox.innerHTML = html;
      const { line, col } = this._cursor();
      const cw = this._charWidth();
      const x = 44 + 14 + col * cw - this.ta.scrollLeft;
      const y = 12 + line * 20 - this.ta.scrollTop + 20;
      this._acBox.style.left = Math.min(x, this.wrap.clientWidth - 200) + "px";
      this._acBox.style.top = Math.max(y, 0) + "px";
      this._acBox.style.display = "block";
      this._acBox.querySelectorAll(".item").forEach((el) => {
        el.addEventListener("mousedown", (e) => {
          e.preventDefault();
          this._acSel = parseInt(el.dataset.i, 10);
          this._commitAC();
        });
      });
    }

    _moveAC(d) {
      if (!this._acBox) return;
      this._acSel = (this._acSel + d + this._acItems.length) % this._acItems.length;
      this._renderAC();
    }

    _closeAC() {
      if (this._acBox) this._acBox.style.display = "none";
      this._acBox = null;
      this._acItems = [];
    }

    _charWidth() {
      if (this._charW != null) return this._charW;
      const cs = getComputedStyle(this.ta);
      const ctx = document.createElement("canvas").getContext("2d");
      ctx.font = cs.font || "13px monospace";
      this._charW = ctx.measureText("M").width;
      return this._charW;
    }

    destroy() {
      this._closeAC();
      if (this.wrap && this.wrap.parentNode) this.wrap.parentNode.removeChild(this.wrap);
    }
  };
})();
