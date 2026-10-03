#!/usr/bin/env python3
"""The web version of the paper: LaTeX blocks of the org file -> one HTML page.

Usage:  tools/tex2html.py ORG AUX OUTDIR [--code DIR] [--out DIR] [--cache DIR]

The page has the look of the web book of the Math 714 notes (sidebar, boxed
statements, folded proofs, citation links), whose stylesheets are vendored in
tools/assets/.  The LaTeX is read from the org file's `latex' blocks, in
order; every Magma block with a #+NAME becomes a folded "Magma check" box at
its place in the stream, holding the code (highlighted by Emacs, from
build/code/NAME.html) and the output of its statement (build/out/LABEL.txt).

Every number -- sections, statements, equations, items, tables, figures,
citation labels -- is LaTeX's own, read from the .aux file of the compiled
paper, so the page and the PDF cannot disagree.  The converter knows exactly
the LaTeX this paper uses; anything else stops the build with its line
number, so that an edit made on Overleaf cannot silently break the page.
"""

import hashlib
import html
import os
import re
import shutil
import subprocess
import sys
import tempfile


class ConversionError(Exception):
    pass


# ---------------------------------------------------------------------------
# The org file: its LaTeX stream, with Magma markers
# ---------------------------------------------------------------------------

def read_org(path):
    """The paper's LaTeX, in order, with a line `\\magmabox{NAME}' for each
    named Magma block, and a map from stream lines to org lines."""
    lines = open(path, encoding="utf-8").read().split("\n")
    stream, origin = [], []
    name = None
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"\s*#\+NAME:\s*(\S+)", line, re.I)
        if m:
            name = m.group(1)
            i += 1
            continue
        m = re.match(r"\s*#\+begin_src\s+(\S+)(.*)", line, re.I)
        if m:
            lang, args = m.group(1), m.group(2)
            j = i + 1
            while not re.match(r"\s*#\+end_src", lines[j], re.I):
                j += 1
            body = [re.sub(r"^(\s*),(\*|#\+|,)", r"\1\2", l) for l in lines[i + 1:j]]
            # a LaTeX block is on the page if it tangles to the paper (the
            # file-wide default) or has :html t; a named Magma block is on the
            # page unless it has :html no, or is a setup- block without :html t
            if lang == "latex" and (":tangle no" not in args or ":html t" in args):
                for k, l in enumerate(body):
                    stream.append(l)
                    origin.append(i + 2 + k)
                stream.append("")           # org-babel's blank line between blocks
                origin.append(j + 1)
            elif lang == "magma" and name and ":html no" not in args \
                    and (not name.startswith("setup-") or ":html t" in args):
                stream.append("\\magmabox{%s}" % name)
                origin.append(i + 1)
                stream.append("")
                origin.append(j + 1)
            name = None
            i = j + 1
            continue
        if line.strip():
            name = None
        i += 1
    return "\n".join(stream) + "\n", origin


# ---------------------------------------------------------------------------
# The .aux file
# ---------------------------------------------------------------------------

def brace_group(s, i):
    """The balanced {...} group starting at s[i] == '{': (content, end)."""
    assert s[i] == "{", s[i:i + 20]
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    raise ConversionError("unbalanced brace at offset %d" % i)


def read_aux(path):
    labels, types, cites = {}, {}, {}
    text = open(path, encoding="utf-8").read()
    for m in re.finditer(r"\\newlabel\{([^}]+)\}", text):
        name = m.group(1)
        if text[m.end()] != "{":
            continue
        payload, _ = brace_group(text, m.end())
        if not payload.startswith("{"):
            continue                # amsart's \newlabel{tocindent..}{<length>}
        first, _ = brace_group(payload, 0)
        if name.endswith("@cref"):
            mm = re.match(r"\[([^\]]*)\]\[[^\]]*\]\[[^\]]*\](.*)", first)
            types[name[:-5]] = mm.group(1)
        else:
            labels[name] = first
    for m in re.finditer(r"\\bibcite\{([^}]+)\}\{\{(.*?)\}\{\}\}", text):
        cites[m.group(1)] = m.group(2)
    return labels, types, cites


# ---------------------------------------------------------------------------
# Inline text
# ---------------------------------------------------------------------------

ACCENTS = {"'": "\u0301", '"': "\u0308", "~": "\u0303", "`": "\u0300",
           "^": "\u0302", "v": "\u030c", "c": "\u0327", "k": "\u0328",
           "=": "\u0304", "u": "\u0306", "H": "\u030b"}

CREF_NAMES = {
    "lemma": ("Lemma", "Lemmas"), "proposition": ("Proposition", "Propositions"),
    "corollary": ("Corollary", "Corollaries"), "remark": ("Remark", "Remarks"),
    "example": ("Example", "Examples"), "definition": ("Definition", "Definitions"),
    "theorem": ("Theorem", "Theorems"), "mainthm": ("Theorem", "Theorems"),
    "maincor": ("Corollary", "Corollaries"), "section": ("Section", "Sections"),
    "subsection": ("Section", "Sections"), "table": ("Table", "Tables"),
    "figure": ("Figure", "Figures"), "enumi": ("item", "items"),
    "enumii": ("item", "items"),
}

STATEMENTS = {"lemma": "Lemma", "proposition": "Proposition",
              "corollary": "Corollary", "remark": "Remark",
              "example": "Example", "definition": "Definition",
              "theorem": "Theorem", "mainthm": "Theorem", "maincor": "Corollary"}
# the web book's box classes
BOX = {"mainthm": "theorem", "maincor": "corollary"}

DISPLAY = {"equation", "equation*", "align", "align*", "gather", "gather*",
           "multline", "multline*"}
NUMBERED_DISPLAY = {"equation", "align", "gather", "multline"}

IGNORED = {"noindent", "centering", "newpage", "medskip", "smallskip",
           "bigskip", "maketitle", "tableofcontents", "FloatBarrier", "par",
           "hfill", "relax", "protect"}


class Converter:
    def __init__(self, stream, origin, aux, code_dir, out_dir, cache_dir,
                 preamble, outdir):
        self.src = stream
        self.origin = origin
        self.labels, self.types, self.cites = aux
        self.code_dir, self.out_dir = code_dir, out_dir
        self.cache_dir, self.preamble, self.outdir = cache_dir, preamble, outdir
        self.sections = []          # (level, number, title html, id)
        self.footnotes = []
        self.section_number = None  # the current section's number, as a string
        self.magma_seen = []
        self.current_statement = None

    # -- errors --------------------------------------------------------------
    def fail(self, pos, msg):
        line = self.src.count("\n", 0, pos)
        org = self.origin[line] if line < len(self.origin) else "?"
        snippet = self.src[pos:pos + 60].split("\n")[0]
        raise ConversionError("org line %s: %s\n    at: %s" % (org, msg, snippet))

    # -- helpers ---------------------------------------------------------------
    def group(self, s, i, base):
        while i < len(s) and s[i] in " \t\n":
            i += 1
        if i >= len(s) or s[i] != "{":
            self.fail(base + i, "expected {")
        return brace_group(s, i)

    def optional(self, s, i):
        j = i
        while j < len(s) and s[j] in " \t":
            j += 1
        if j < len(s) and s[j] == "[":
            depth, k = 0, j
            while k < len(s):
                if s[k] == "{":
                    depth += 1
                elif s[k] == "}":
                    depth -= 1
                elif s[k] == "]" and depth == 0:
                    return s[j + 1:k], k + 1
                k += 1
        return None, i

    def star_optional(self, s, i):
        """amsrefs' locator: \\cite{K}*{Loc}."""
        if i < len(s) and s[i] == "*" and i + 1 < len(s) and s[i + 1] == "{":
            loc, j = brace_group(s, i + 1)
            return loc, j
        return None, i

    def number(self, label, pos):
        if label not in self.labels:
            self.fail(pos, "label %s is not in the .aux file" % label)
        return self.labels[label]

    # -- references ------------------------------------------------------------
    def ref_text(self, label, pos):
        num = self.number(label, pos)
        kind = self.types.get(label, "")
        return num, kind

    def href(self, label):
        kind = self.types.get(label, "")
        if kind == "equation":
            return "#mjx-eqn:" + label
        return "#" + label

    def cref(self, labels, pos, capital=False):
        groups = []
        for label in labels:
            num, kind = self.ref_text(label, pos)
            if groups and groups[-1][0] == kind:
                groups[-1][1].append((num, label))
            else:
                groups.append((kind, [(num, label)]))
        parts = []
        for kind, refs in groups:
            # as cleveref (sort&compress): sorted, and a run of three or more
            # consecutive numbers is "X to Y"
            key = lambda r: [int(p) if p.isdigit() else p for p in re.split(r"[.]", r[0])]
            try:
                refs = sorted(refs, key=key)
            except TypeError:
                pass
            def link(ref):
                num, label = ref
                shown = "(%s)" % num if kind in ("equation",) else num
                return '<a href="%s">%s</a>' % (self.href(label), shown)
            def successor(a, b):
                pa, pb = a[0].split("."), b[0].split(".")
                return (len(pa) == len(pb) and pa[:-1] == pb[:-1] and pa[-1].isdigit()
                        and pb[-1].isdigit() and int(pb[-1]) == int(pa[-1]) + 1)
            links, k = [], 0
            while k < len(refs):
                m = k
                while m + 1 < len(refs) and successor(refs[m], refs[m + 1]):
                    m += 1
                if m - k >= 2:
                    links.append(link(refs[k]) + " to " + link(refs[m]))
                    k = m + 1
                else:
                    links.append(link(refs[k]))
                    k += 1
            if kind == "equation":
                name = ""
            else:
                if kind not in CREF_NAMES:
                    self.fail(pos, "no \\cref name for type %s" % kind)
                singular, plural = CREF_NAMES[kind]
                name = (singular if len(refs) == 1 else plural) + "&nbsp;"
                if capital:
                    name = name[0].upper() + name[1:]
            parts.append(name + join_and(links))
        return join_and(parts)

    def cite(self, items, pos):
        out = []
        for key, loc in items:
            if key not in self.cites:
                self.fail(pos, "citation %s is not in the .aux file" % key)
            label = self.cites[key].replace("$^{+}$", "<sup>+</sup>")
            a = '<a class="ec-cite" href="#bib-%s">%s</a>' % (key, label)
            out.append(a + (", " + self.inline(loc, pos) if loc else ""))
        return "[" + "; ".join(out) + "]"

    # -- inline LaTeX -> HTML --------------------------------------------------
    def inline(self, s, base=0):
        out = []
        i = 0
        n = len(s)
        while i < n:
            c = s[i]
            if c == "%":
                j = s.find("\n", i)
                i = n if j < 0 else j + 1
                # a comment swallows its newline and the next line's indent
                while i < n and s[i] in " \t":
                    i += 1
                continue
            if c == "$":
                if s.startswith("$$", i):
                    self.fail(base + i, "$$ display math")
                j = i + 1
                while j < n and s[j] != "$":
                    if s[j] == "\\":
                        j += 1
                    j += 1
                if j >= n:
                    self.fail(base + i, "unterminated $")
                out.append("\\(" + self.math(s[i + 1:j], base + i) + "\\)")
                i = j + 1
                continue
            if c == "\\":
                if s.startswith("\\(", i):
                    j = s.find("\\)", i)
                    out.append("\\(" + self.math(s[i + 2:j], base + i) + "\\)")
                    i = j + 2
                    continue
                m = re.match(r"\\([A-Za-z@]+)\*?|\\(.)", s[i:])
                name = m.group(1) or m.group(2)
                starred = m.group(0).endswith("*") and m.group(1) is not None
                j = i + len(m.group(0))
                html_, j = self.command(name, starred, s, j, base, i)
                out.append(html_)
                i = j
                continue
            if c == "{" or c == "}":
                i += 1
                continue
            if c == "~":
                out.append("&nbsp;")
                i += 1
                continue
            if s.startswith("---", i):
                out.append("&mdash;")
                i += 3
                continue
            if s.startswith("--", i):
                out.append("&ndash;")
                i += 2
                continue
            if s.startswith("``", i):
                out.append("&ldquo;")
                i += 2
                continue
            if s.startswith("''", i):
                out.append("&rdquo;")
                i += 2
                continue
            if c == "`":
                out.append("&lsquo;")
                i += 1
                continue
            if c == "'":
                out.append("&rsquo;")
                i += 1
                continue
            if c == "&":
                self.fail(base + i, "alignment & outside a table")
            out.append(html.escape(c, quote=False))
            i += 1
        return "".join(out)

    def command(self, name, starred, s, j, base, start):
        pos = base + start
        if name in IGNORED:
            while j < len(s) and s[j] in " \t":
                j += 1
            return "", j
        if name == "setcounter":
            _, j = self.group(s, j, base)
            _, j = self.group(s, j, base)
            return "", j
        if name in ("emph", "textit"):
            g, j = self.group(s, j, base)
            return "<em>%s</em>" % self.inline(g, base + j), j
        if name == "textbf":
            g, j = self.group(s, j, base)
            return "<strong>%s</strong>" % self.inline(g, base + j), j
        if name == "texttt":
            g, j = self.group(s, j, base)
            return "<code>%s</code>" % self.inline(g, base + j), j
        if name == "textsf":
            g, j = self.group(s, j, base)
            return '<span class="paper-sf">%s</span>' % self.inline(g, base + j), j
        if name == "cdef":
            g, j = self.group(s, j, base)
            return '<dfn class="ec-cdef">%s</dfn>' % self.inline(g, base + j), j
        if name == "Magma":
            if s.startswith("{}", j):
                j += 2
            return "<code>Magma</code>", j
        if name == "href":
            url, j = self.group(s, j, base)
            text, j = self.group(s, j, base)
            return '<a href="%s">%s</a>' % (html.escape(url), self.inline(text, base + j)), j
        if name == "url":
            url, j = self.group(s, j, base)
            return '<a href="%s"><code>%s</code></a>' % (html.escape(url), html.escape(url)), j
        if name == "mclabel":
            g, j = self.group(s, j, base)
            return ('<a href="https://beta.lmfdb.org/ModularCurve/Q/%s"><code>%s</code></a>'
                    % (g, g)), j
        if name == "texorpdfstring":
            g, j = self.group(s, j, base)
            _, j = self.group(s, j, base)
            return self.inline(g, base + j), j
        if name in ("cref", "Cref"):
            g, j = self.group(s, j, base)
            return self.cref([x.strip() for x in g.split(",")], pos, name == "Cref"), j
        if name in ("eqref", "ref"):
            g, j = self.group(s, j, base)
            num = self.number(g, pos)
            shown = "(%s)" % num if name == "eqref" else num
            return '<a class="ec-eqref" href="%s">%s</a>' % (self.href(g), shown), j
        if name == "cite":
            g, j = self.group(s, j, base)
            loc, j = self.star_optional(s, j)
            keys = [k.strip() for k in g.split(",")]
            items = [(k, None) for k in keys[:-1]] + [(keys[-1], loc)]
            return self.cite(items, pos), j
        if name == "cites":
            items = []
            while j < len(s) and s[j] == "{":
                g, j = brace_group(s, j)
                loc, j = self.star_optional(s, j)
                keys = [k.strip() for k in g.split(",")]
                items += [(k, None) for k in keys[:-1]] + [(keys[-1], loc)]
            return self.cite(items, pos), j
        if name == "footnote":
            g, j = self.group(s, j, base)
            self.footnotes.append(self.inline(g, base + j))
            k = len(self.footnotes)
            return ('<sup class="paper-fnref"><a id="fnref%d" href="#fn%d">%s</a></sup>'
                    % (k, k, roman(k))), j
        # a control word with no argument swallows the spaces after it
        words = {"ndash": "&ndash;", "mdash": "&mdash;", "dots": "&hellip;",
                 "ldots": "&hellip;", "S": "&sect;"}
        if name in words:
            while j < len(s) and s[j] in " \t":
                j += 1
            return words[name], j
        if name in (",", " ", "@", "/", "-", "\n"):
            return (" " if name in (" ", "\n") else ("&thinsp;" if name == "," else "")), j
        if name in ("%", "&", "#", "_", "$", "{", "}"):
            return html.escape(name), j
        if name in ACCENTS:
            if j < len(s) and s[j] == "{":
                g, j = brace_group(s, j)
            else:
                g, j = s[j], j + 1
            base_char = g.replace("\\i", "i")
            return base_char + ACCENTS[name], j
        if name == "label":
            g, j = self.group(s, j, base)
            return '<a id="%s"></a>' % g, j
        if name == "magmabox":
            self.fail(pos, "a Magma block inside a paragraph")
        self.fail(pos, "unknown command \\%s" % name)

    # -- math ------------------------------------------------------------------
    def math(self, s, pos):
        """Math goes to MathJax as is, HTML-escaped; macros come from
        macros.js.  Only text-mode commands inside \\text{...} are refused."""
        for m in re.finditer(r"\\(cref|Cref|cite|eqref|ref)\b", s):
            self.fail(pos, "\\%s inside math" % m.group(1))
        return html.escape(s, quote=False)

    # -- blocks ----------------------------------------------------------------
    def blocks(self, s, base=0):
        """LaTeX -> a list of HTML blocks; paragraphs are wrapped in <p>."""
        out, para = [], []

        def flush():
            text = "".join(para).strip()
            if text:
                out.append("<p>\n%s\n</p>" % text)
            para.clear()

        i, n = 0, len(s)
        while i < n:
            # a blank line ends the paragraph
            m = re.match(r"[ \t]*\n([ \t]*\n)+", s[i:])
            if not m and (i == 0 or s[i - 1] == "\n"):
                m = re.match(r"([ \t]*\n)+", s[i:])
            if m:
                flush()
                i += len(m.group(0))
                continue
            m = re.match(r"\\begin\{([^}]+)\}", s[i:])
            if m:
                env = m.group(1)
                inner_start = i + len(m.group(0))
                end = self.find_end(s, env, inner_start, base)
                inner = s[inner_start:end]
                after = end + len("\\end{%s}" % env)
                if env in DISPLAY:
                    flush()
                    out.append(self.display(env, inner, base + inner_start))
                elif env in ("enumerate", "itemize"):
                    flush()
                    out.append(self.lst(env, inner, base + inner_start))
                else:
                    flush()
                    out.append(self.environment(env, inner, base + inner_start))
                i = after
                continue
            if s.startswith("\\[", i):
                j = s.find("\\]", i)
                flush()
                inner = s[i + 2:j].strip("\n")
                if inner.strip().startswith("\\begin{tikzcd}"):
                    # a commutative diagram: MathJax has no tikz-cd, so it is drawn
                    # by LaTeX, as in the web book
                    svg = self.tikz_svg(inner.strip())
                    out.append('<div class="ec-diagram"><img class="ec-tikz" src="figures/%s" alt="diagram"%s/></div>'
                               % (svg, self.tikz_style(svg)))
                else:
                    out.append("\\[\n%s\n\\]" % self.math(inner, base + i))
                i = j + 2
                continue
            m = re.match(r"\\(section|subsection)(\*?)", s[i:])
            if m:
                flush()
                j = i + len(m.group(0))
                title, j = self.group(s, j, base)
                label = None
                mm = re.match(r"\s*\\label\{([^}]+)\}", s[j:])
                if mm:
                    label = mm.group(1)
                    j += len(mm.group(0))
                out.append(self.heading(m.group(1), m.group(2) == "*", title, label, base + i))
                i = j
                continue
            m = re.match(r"\\magmabox\{([^}]+)\}", s[i:])
            if m:
                flush()
                out.append(self.magmabox(m.group(1)))
                i += len(m.group(0))
                continue
            # one line of paragraph text: up to the next newline, but a
            # \begin, \[ or \section in mid-line is handled above next time
            j = i
            while j < n and s[j] != "\n":
                if s[j] == "\\" and (s.startswith("\\begin{", j) or s.startswith("\\[", j)
                                     or s.startswith("\\section", j)
                                     or s.startswith("\\subsection", j)
                                     or s.startswith("\\magmabox", j)):
                    break
                if s[j] == "\\":
                    j += 2
                    continue
                if s[j] == "$":
                    # skip inline math as a unit
                    k = j + 1
                    while k < n and s[k] != "$":
                        if s[k] == "\\":
                            k += 1
                        k += 1
                    j = k + 1
                    continue
                if s[j] == "{":
                    _, j = brace_group(s, j)
                    continue
                j += 1
            if j < n and s[j] == "\n":
                j += 1
            para.append(self.inline(s[i:j], base + i))
            if i == j:
                self.fail(base + i, "converter stuck")
            i = j
        flush()
        return out

    def find_end(self, s, env, start, base):
        depth, i = 1, start
        pat = re.compile(r"\\(begin|end)\{%s\}" % re.escape(env))
        while True:
            m = pat.search(s, i)
            if not m:
                self.fail(base + start, "no \\end{%s}" % env)
            depth += 1 if m.group(1) == "begin" else -1
            if depth == 0:
                return m.start()
            i = m.end()

    # -- sections ----------------------------------------------------------------
    def heading(self, kind, star, title, label, pos):
        title_html = self.inline(title, pos)
        level = 2 if kind == "section" else 3
        if star:
            ident = label or "s-" + re.sub(r"[^a-z0-9]+", "-", strip_tags(title_html).lower()).strip("-")
            self.sections.append((level, "", title_html, ident))
            return '<h%d id="%s" class="paper-unnumbered">%s</h%d>' % (level, ident, title_html, level)
        # LaTeX's counters, kept here too, for the sections without a \label;
        # where there is one, the two must agree.
        if kind == "section":
            self.counter_section = getattr(self, "counter_section", 0) + 1
            self.counter_subsection = 0
            self.counter_equation = 0
            num = str(self.counter_section)
        else:
            self.counter_subsection = getattr(self, "counter_subsection", 0) + 1
            num = "%d.%d" % (self.counter_section, self.counter_subsection)
        if label:
            # LaTeX's number wins; the counters follow it
            num = self.number(label, pos)
            parts = [int(x) for x in num.split(".")]
            self.counter_section = parts[0]
            if len(parts) > 1:
                self.counter_subsection = parts[1]
        label = label or "s" + num
        if kind == "section":
            self.section_number = num
        self.sections.append((level, num, title_html, label))
        sid = "" if label == "s" + num else ' id="s%s"' % num
        return ('<h%d id="%s"><span class="section-number"%s>%s</span> %s</h%d>'
                % (level, label, sid, num, title_html, level))

    # -- statements and other environments ----------------------------------------
    def environment(self, env, inner, pos):
        if env in STATEMENTS:
            return self.statement(env, inner, pos)
        if env == "proof":
            title, k = self.optional(inner, 0)
            head = "Proof" if title is None else self.inline(title, pos)
            body = "\n".join(self.blocks(inner[k:], pos + k))
            return ('<details class="ec-proof">\n<summary><span class="ec-proof-head">%s.</span>'
                    '</summary>\n%s\n</details>' % (head, body))
        if env == "table":
            return self.table(inner, pos)
        if env == "figure":
            return self.figure(inner, pos)
        if env == "abstract":
            return ('<div class="paper-abstract"><p class="paper-abstract-head">Abstract</p>\n%s\n</div>'
                    % "\n".join(self.blocks(inner, pos)))
        if env == "bibdiv":
            return self.bibliography(inner, pos)
        if env == "document":
            return "\n".join(self.blocks(inner, pos))
        self.fail(pos, "unknown environment %s" % env)

    def statement(self, env, inner, pos):
        title, k = self.optional(inner, 0)
        m = re.match(r"\s*\\label\{([^}]+)\}", inner[k:])
        # LaTeX's counters: one for the numbered statements, within sections,
        # and one for the main results; a \label resets them to LaTeX's value
        main = env in ("mainthm", "maincor")
        if main:
            self.counter_main = getattr(self, "counter_main", 0) + 1
            num = str(self.counter_main)
        else:
            if getattr(self, "counter_section_for_thm", None) != self.section_number:
                self.counter_thm = 0
                self.counter_section_for_thm = self.section_number
            self.counter_thm += 1
            num = "%s.%d" % (self.section_number, self.counter_thm)
        if m:
            label = m.group(1)
            k += len(m.group(0))
            num = self.number(label, pos)
            if main:
                self.counter_main = int(num)
            else:
                self.counter_thm = int(num.split(".")[-1])
        else:
            label = "%s-%s" % (env, num)
        self.current_statement = label
        blocks = self.blocks(inner[k:], pos + k)
        head = '<span class="ec-thm-head"><span class="ec-thm-name">%s %s</span>' % (STATEMENTS[env], num)
        if title:
            head += ' <span class="ec-thm-title">(%s)</span>' % self.inline(title, pos)
        head += ".</span> "
        if blocks and blocks[0].startswith("<p>\n"):
            blocks[0] = "<p>\n" + head + blocks[0][4:]
        else:
            blocks.insert(0, "<p>\n" + head + "\n</p>")
        return ('<div class="ec-thm ec-%s" id="%s">\n%s\n</div>'
                % (BOX.get(env, env), label, "\n".join(blocks)))

    def lst(self, env, inner, pos):
        opts, k = self.optional(inner, 0)
        items = split_items(inner[k:])
        if items[0].strip():
            self.fail(pos, "text before the first \\item")
        tag = "ol" if env == "enumerate" else "ul"
        self.list_depth = getattr(self, "list_depth", 0) + 1
        lis = []
        for index, item in enumerate(items[1:]):
            ident, label_html = "", ""
            if tag == "ol":
                shown = str(index + 1) if self.list_depth == 1 else "abcdefghij"[index]
                label_html = '<span class="paper-item-label">(%s)</span> ' % shown
            m = re.match(r"\s*\\label\{([^}]+)\}", item)
            if m:
                label = m.group(1)
                ident = ' id="%s"' % label
                num = self.number(label, pos)
                if not num.endswith(shown):
                    self.fail(pos, "item %s is (%s) in LaTeX, (%s) here" % (label, num, shown))
                item = item[len(m.group(0)):]
            blocks = self.blocks(item, pos)
            body = "\n".join(blocks)
            if len(blocks) == 1 and blocks[0].startswith("<p>\n"):
                body = blocks[0][4:-5]
            lis.append("<li%s>%s%s</li>" % (ident, label_html, body))
        self.list_depth -= 1
        cls = "org-ol paper-labelled" if tag == "ol" else "org-ul"
        return "<%s class=\"%s\">\n%s\n</%s>" % (tag, cls, "\n".join(lis), tag)

    # -- displays ------------------------------------------------------------------
    def display(self, env, inner, pos):
        """Every numbered row gets LaTeX's own number as an explicit \\tag, so
        MathJax numbers nothing itself; its \\label stays, for MathJax's
        anchor (mjx-eqn:LABEL)."""
        body = inner.strip("\n")
        if env in NUMBERED_DISPLAY:
            rows = split_rows(body)
            new_rows = []
            for row in rows:
                if "\\nonumber" in row or "\\notag" in row:
                    new_rows.append(row)
                    continue
                self.counter_equation = getattr(self, "counter_equation", 0) + 1
                num = "%s.%d" % (self.section_number, self.counter_equation)
                m = re.search(r"\\label\{([^}]+)\}", row)
                if m:
                    num = self.number(m.group(1), pos)
                    self.counter_equation = int(num.split(".")[-1])
                new_rows.append(row.rstrip() + " \\tag{%s}" % num)
            body = "\\\\\n".join(new_rows)
        return "\\begin{%s}\n%s\n\\end{%s}" % (env, self.math(body, pos), env)

    # -- tables ------------------------------------------------------------------------
    def table(self, inner, pos):
        _, k = self.optional(inner, 0)          # the float placement [ht]
        inner = inner[k:]
        caption, label = None, None
        m = re.search(r"\\caption\{", inner)
        if m:
            caption, end = brace_group(inner, m.end() - 1)
            inner = inner[:m.start()] + inner[end:]
        m = re.search(r"\\label\{([^}]+)\}", inner)
        if m:
            label = m.group(1)
            inner = inner[:m.start()] + inner[m.end():]
        m = re.search(r"\\begin\{tabular\}", inner)
        if not m:
            self.fail(pos, "a table without a tabular")
        spec, k = brace_group(inner, m.end())
        end = inner.find("\\end{tabular}", k)
        rows_html = self.tabular(spec, inner[k:end], pos)
        rest = (inner[:m.start()] + inner[end + len("\\end{tabular}"):])
        rest = re.sub(r"\\(centering|tablesetup)\b", "", rest).strip()
        if rest:
            self.fail(pos, "unexpected material in a table: %s" % rest[:40])
        num = self.number(label, pos) if label else ""
        cap = ('<figcaption><span class="ec-figure-name">Table %s.</span> %s</figcaption>'
               % (num, self.inline(caption, pos))) if caption else ""
        return ('<figure class="ec-figure paper-table" id="%s">\n<div class="paper-table-scroll">'
                '<table>\n%s\n</table></div>\n%s\n</figure>' % (label or "", rows_html, cap))

    def tabular(self, spec, body, pos):
        cols = parse_colspec(spec)
        rows, pending = [], []
        header_next = False
        text = body
        # rules and row markers on their own; rows end in \\
        rows = split_rows(text)
        out = []
        for raw in rows:
            classes = []
            while True:
                raw = raw.lstrip()
                m = re.match(r"\\(toprule|headrule|rowsep|bottomrule|midrule|headrow)\b|\\padrows\{[^}]*\}|%[^\n]*\n", raw)
                if not m:
                    break
                if m.group(1) == "headrow":
                    classes.append("paper-head")
                elif m.group(1) in ("headrule", "midrule"):
                    classes.append("paper-rule-heavy")
                elif m.group(1) == "rowsep":
                    classes.append("paper-rule-light")
                raw = raw[m.end():]
            if not raw.strip():
                continue
            cells = split_cells(raw)
            tds, col = [], 0
            for cell in cells:
                cell = cell.strip()
                span, align = 1, None
                m = re.match(r"\\multicolumn\{(\d+)\}", cell)
                if m:
                    span = int(m.group(1))
                    cspec, k = brace_group(cell, m.end())
                    content, _ = brace_group(cell, k)
                    cell = content
                    left_rule, right_rule = cspec.startswith(("I", ":")), cspec.endswith(("I", ":"))
                cls = []
                last = col + span - 1
                if last < len(cols) and cols[last]["right"]:
                    cls.append("paper-vr-" + cols[last]["right"])
                if col < len(cols) and col == 0 and cols[0]["left"]:
                    cls.append("paper-vl-" + cols[0]["left"])
                content = self.cell(cell, pos)
                tag = "th" if "paper-head" in classes else "td"
                tds.append('<%s%s%s>%s</%s>' % (
                    tag, ' colspan="%d"' % span if span > 1 else "",
                    ' class="%s"' % " ".join(cls) if cls else "", content, tag))
                col += span
            out.append('<tr%s>%s</tr>' % (' class="%s"' % " ".join(classes) if classes else "",
                                         "".join(tds)))
        return "\n".join(out)

    def cell(self, cell, pos):
        m = re.match(r"\s*\\tabmatrix\{", cell)
        if m:
            g, _ = brace_group(cell, m.end() - 1)
            return "\\(%s\\)" % self.math("\\begin{pmatrix*}[r] %s\\end{pmatrix*}" % g, pos)
        return self.inline(cell, pos)

    # -- figures -------------------------------------------------------------------------
    def figure(self, inner, pos):
        _, k = self.optional(inner, 0)
        inner = inner[k:]
        caption, label = None, None
        m = re.search(r"\\caption\{", inner)
        if m:
            caption, end = brace_group(inner, m.end() - 1)
            inner = inner[:m.start()] + inner[end:]
        m = re.search(r"\\label\{([^}]+)\}", inner)
        if m:
            label = m.group(1)
            inner = inner[:m.start()] + inner[m.end():]
        m = re.search(r"\\begin\{tikzcd\}(\[[^\]]*\])?", inner)
        if not m:
            self.fail(pos, "a figure without a tikzcd")
        end = inner.find("\\end{tikzcd}")
        picture = inner[m.start():end + len("\\end{tikzcd}")]
        svg = self.tikz_svg(picture)
        num = self.number(label, pos)
        return ('<figure class="ec-figure" id="%s">\n<img class="ec-tikz" src="figures/%s" alt="Figure %s"%s/>\n'
                '<figcaption><span class="ec-figure-name">Figure %s.</span> %s</figcaption>\n</figure>'
                % (label, svg, num, self.tikz_style(svg), num, self.inline(caption, pos)))

    def tikz_svg(self, picture):
        doc = ("\\documentclass[12pt,border=4pt]{standalone}\n" + self.preamble
               + "\n\\begin{document}\n" + picture + "\n\\end{document}\n")
        key = hashlib.sha1(doc.encode()).hexdigest()[:16]
        name = "tikz-%s.svg" % key
        cached = os.path.abspath(os.path.join(self.cache_dir, name))
        if not os.path.exists(cached):
            os.makedirs(self.cache_dir, exist_ok=True)
            with tempfile.TemporaryDirectory() as tmp:
                with open(os.path.join(tmp, "fig.tex"), "w") as f:
                    f.write(doc)
                r = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "fig.tex"],
                                   cwd=tmp, capture_output=True, text=True)
                if r.returncode:
                    raise ConversionError("tikz picture failed to compile:\n" + r.stdout[-2000:])
                subprocess.run(["pdftocairo", "-svg", "fig.pdf", cached], cwd=tmp, check=True)
        os.makedirs(os.path.join(self.outdir, "figures"), exist_ok=True)
        shutil.copy(cached, os.path.join(self.outdir, "figures", name))
        return name

    def tikz_style(self, name):
        """The picture's width in em of the paper's 12pt text, as the web book
        sizes its pictures (book.css reads --ec-w)."""
        head = open(os.path.join(self.cache_dir, name), encoding="utf-8").read(400)
        m = re.search(r'width="([0-9.]+)pt"', head)
        return ' style="--ec-w: %.2fem"' % (float(m.group(1)) / 12) if m else ""

    # -- Magma ---------------------------------------------------------------------------
    def magmabox(self, name):
        self.magma_seen.append(name)
        path = os.path.join(self.code_dir, name + ".html")
        if not os.path.exists(path):
            raise ConversionError("no highlighted code for Magma block %s (%s)" % (name, path))
        code = open(path, encoding="utf-8").read()
        meta_path = os.path.join(self.code_dir, name + ".meta")
        meta = dict(l.split("\t", 1) for l in open(meta_path, encoding="utf-8").read().splitlines()
                    if "\t" in l) if os.path.exists(meta_path) else {}
        label = meta.get("label", "")
        title = "Magma"
        if label and label in self.labels:
            kind = self.types.get(label, "")
            num = self.number(label, 0)
            what = "(%s)" % num if kind == "equation" else "%s %s" % (
                CREF_NAMES.get(kind, ("", ""))[0].capitalize(), num)
            title = "Magma check: " + what.strip()
        if meta.get("title") and (not label or label not in self.labels):
            title = meta["title"]
        open_attr = " open" if meta.get("open") == "t" else ""
        out_html = ""
        if label and not name.startswith("setup-"):
            out_path = os.path.join(self.out_dir, label + ".txt")
            if not os.path.exists(out_path):
                raise ConversionError("no recorded output for %s (%s)" % (name, out_path))
            out_html = ('<p class="paper-output-head">Output</p>\n<pre class="example paper-output">%s</pre>'
                        % html.escape(open(out_path, encoding="utf-8").read().rstrip("\n")))
        file_ = meta.get("file", "")
        file_html = (' <a class="paper-code-file" href="%s">%s</a>' % (file_, file_)) if file_ else ""
        prose_path = os.path.join(self.code_dir, name + ".prose.html")
        prose = open(prose_path, encoding="utf-8").read().strip() if os.path.exists(prose_path) else ""
        if prose:
            prose = '<div class="paper-code-note">\n%s\n</div>' % prose
        return ('<details class="ec-code" id="code-%s"%s>\n<summary><span class="ec-code-head">%s</span>%s</summary>\n'
                '%s\n%s\n%s\n</details>' % (name, open_attr, title, file_html, prose, code.strip(), out_html))

    # -- bibliography -------------------------------------------------------------------
    def bibliography(self, inner, pos):
        m = re.search(r"\\begin\{biblist\}", inner)
        end = inner.find("\\end{biblist}")
        body = inner[m.end():end]
        entries = []
        for mm in re.finditer(r"\\bib\{([^}]+)\}\{([^}]+)\}\{", body):
            fields_src, _ = brace_group(body, mm.end() - 1)
            entries.append((mm.group(1), mm.group(2), parse_bib_fields(fields_src)))
        items = []
        for key, kind, fields in entries:
            label = self.cites.get(key, key).replace("$^{+}$", "<sup>+</sup>")
            items.append('<dt id="bib-%s">[%s]</dt>\n<dd>%s</dd>' % (key, label, self.bib_entry(kind, fields, pos)))
        self.sections.append((2, "", "References", "references"))
        return ('<div class="ec-references" id="references">\n<h2>References</h2>\n'
                '<dl class="ec-bibliography">\n%s\n</dl>\n</div>' % "\n".join(items))

    def bib_entry(self, kind, f, pos):
        def get(k):
            v = f.get(k)
            return self.inline(v[0], pos) if v else None
        parts = []
        authors = [self.inline(a, pos) for a in f.get("author", [])]
        if authors:
            names = [flip_name(a) for a in authors]
            parts.append(join_and(names))
        title = get("title")
        if title:
            parts.append("<em>%s</em>" % title)
        if kind == "article":
            j = get("journal") or ""
            v = get("volume")
            d = get("date")
            s = j
            if v:
                s += " <strong>%s</strong>" % v
            if d:
                s += " (%s)" % d
            if get("number"):
                s += ", no.&nbsp;%s" % get("number")
            if get("pages"):
                s += ", %s" % get("pages")
            parts.append(s)
        else:
            for k in ("booktitle", "series", "edition", "publisher", "address", "organization", "school"):
                if get(k):
                    parts.append(get(k))
            if get("volume"):
                parts.append("vol.&nbsp;%s" % get("volume"))
            if get("pages"):
                parts.append(get("pages"))
            if get("date"):
                parts.append(get("date"))
        for k in ("note", "eprint", "status"):
            if get(k):
                parts.append(get(k))
        if f.get("doi"):
            d = f["doi"][0]
            parts.append('<a href="https://doi.org/%s">doi:%s</a>' % (d, html.escape(d)))
        if f.get("url"):
            u = f["url"][0]
            parts.append('<a href="%s"><code>%s</code></a>' % (html.escape(u), html.escape(u)))
        return ", ".join(p for p in parts if p) + "."


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

def join_and(xs):
    if len(xs) <= 1:
        return "".join(xs)
    if len(xs) == 2:
        return xs[0] + " and " + xs[1]
    return ", ".join(xs[:-1]) + " and " + xs[-1]


def roman(k):
    return ["i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x"][k - 1]


def strip_tags(s):
    return re.sub(r"<[^>]+>", "", s)


def flip_name(name):
    if "," in name:
        last, first = name.split(",", 1)
        return first.strip() + " " + last.strip()
    return name


def split_items(body):
    """Split a list body at its own \\item's, not at those of nested lists."""
    parts, depth, last = [], 0, 0
    for m in re.finditer(r"\\begin\{(enumerate|itemize)\}|\\end\{(enumerate|itemize)\}|\\item\b", body):
        tok = m.group(0)
        if tok.startswith("\\begin"):
            depth += 1
        elif tok.startswith("\\end"):
            depth -= 1
        elif depth == 0:
            parts.append(body[last:m.start()])
            last = m.end()
    parts.append(body[last:])
    return parts


def split_rows(body):
    rows, depth, cur, i = [], 0, "", 0
    while i < len(body):
        if body.startswith("\\\\", i) and depth == 0:
            rows.append(cur)
            cur = ""
            i += 2
            continue
        c = body[i]
        if c == "\\" and i + 1 < len(body):
            cur += body[i:i + 2]
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        cur += c
        i += 1
    if cur.strip():
        rows.append(cur)
    return rows


def split_cells(row):
    cells, depth, cur, i, math = [], 0, "", 0, False
    while i < len(row):
        c = row[i]
        if c == "\\" and i + 1 < len(row):
            cur += row[i:i + 2]
            i += 2
            continue
        if c == "$":
            math = not math
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        if c == "&" and depth == 0 and not math:
            cells.append(cur)
            cur = ""
        else:
            cur += c
        i += 1
    cells.append(cur)
    return cells


def parse_colspec(spec):
    """Columns of a tabular spec, with the rule on each side:
    'I' heavy black, ':' light gray, '|' black."""
    cols, pending = [], None
    for ch in spec.replace(" ", ""):
        if ch in "lcr":
            cols.append({"align": ch, "left": pending, "right": None})
            pending = None
        else:
            kind = {"I": "heavy", ":": "light", "|": "black"}[ch]
            if cols and cols[-1]["right"] is None:
                cols[-1]["right"] = kind
                if pending is None:
                    pending = None
            else:
                pending = kind
    return cols


def parse_bib_fields(src):
    fields = {}
    i = 0
    while i < len(src):
        m = re.match(r"\s*([a-z]+)\s*=\s*\{", src[i:])
        if not m:
            break
        val, j = brace_group(src, i + m.end() - 1)
        fields.setdefault(m.group(1), []).append(val)
        i = j
        while i < len(src) and src[i] in ", \n\t":
            i += 1
    return fields


# ---------------------------------------------------------------------------
# The page
# ---------------------------------------------------------------------------

def macros_js(preamble):
    """The paper's math macros for MathJax, read from its preamble."""
    macros = {}
    for m in re.finditer(r"\\(?:re)?newcommand\{\\([A-Za-z]+)\}(?:\[(\d)\])?\{", preamble):
        body, _ = brace_group(preamble, m.end() - 1)
        macros[m.group(1)] = (body, int(m.group(2) or 0))
    for m in re.finditer(r"\\DeclareMathOperator\{\\([A-Za-z]+)\}\{", preamble):
        body, _ = brace_group(preamble, m.end() - 1)
        macros[m.group(1)] = ("\\operatorname{%s}" % body, 0)
    # text-mode or package macros MathJax needs spelled out
    macros["colonequals"] = ("\\coloneqq", 0)
    macros["sfa"] = ("\\mathsf{a}", 0)
    macros["tabmatrix"] = ("\\begin{pmatrix*}[r] #1\\end{pmatrix*}", 1)
    for name in ("cdef", "Magma", "mclabel", "rowsep", "headrule", "tablesetup",
                 "padrows", "heavyvrule", "headrow"):
        macros.pop(name, None)
    lines = []
    for name, (body, n) in sorted(macros.items()):
        js_body = body.replace("\\", "\\\\").replace('"', '\\"')
        lines.append('      "%s": %s' % (name, '"%s"' % js_body if n == 0 else '["%s",%d]' % (js_body, n)))
    return ("/* GENERATED by tools/tex2html.py from the preamble of 7-adic-settlers.tex. */\n"
            "window.MathJax = {\n  tex: {\n    tags: 'ams',\n    packages: {'[+]': ['mathtools']},\n"
            "    macros: {\n" + ",\n".join(lines) + "\n    }\n  },\n"
            "  options: { ignoreHtmlClass: 'tex2jax_ignore', processHtmlClass: 'tex2jax_process' }\n};\n")


def front_matter(conv, preamble):
    def arg(cmd):
        m = re.search(r"\\%s\{" % cmd, preamble)
        g, _ = brace_group(preamble, m.end() - 1)
        return g
    title = conv.inline(" ".join(arg("title").split()))
    authors = []
    for m in re.finditer(r"\\author\{", preamble):
        g, _ = brace_group(preamble, m.end() - 1)
        authors.append(conv.inline(g))
    return title, authors


def page(conv, title, authors, body):
    toc = []
    for level, num, text, ident in conv.sections:
        cls = "ec-toc-level-1" if level == 2 else "ec-toc-level-2"
        # the sidebar is links already: no links (from \\cref) inside its entries
        text = strip_tags(text).replace("&nbsp;", " ")
        toc.append('<li class="%s"><a href="#%s"><span class="ec-toc-num">%s</span>'
                   '<span class="ec-toc-text">%s</span></a></li>' % (cls, ident, num, text))
    footnotes = ""
    if conv.footnotes:
        footnotes = ('<div class="paper-footnotes"><ol>%s</ol></div>' % "".join(
            '<li id="fn%d"><sup>%s</sup> %s <a href="#fnref%d">&#8617;</a></li>' % (k, roman(k), t, k)
            for k, t in enumerate(conv.footnotes, 1)))
    plain_title = strip_tags(title).replace("\\(", "").replace("\\)", "")
    return """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>%(plain)s</title>
<link rel="stylesheet" type="text/css" href="org-css.css"/>
<link rel="stylesheet" type="text/css" href="book.css"/>
<link rel="stylesheet" type="text/css" href="paper.css"/>
<script src="macros.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml-full.js"></script>
<script defer src="org-code.js"></script>
<script defer src="book.js"></script>
</head>
<body>
<div id="preamble" class="status">
<nav class="ec-sidebar" id="ec-sidebar" aria-label="Contents">
<a class="ec-book-title" href="#top">%(title)s</a>
<p class="ec-book-subtitle">%(authors)s</p>
<ol class="ec-toc">
<li class="ec-toc-chapter is-current"><ol class="ec-toc-sections">
%(toc)s
</ol></li>
</ol>
<p class="paper-sidebar-links"><a href="7-adic-settlers.pdf">PDF</a> &middot; <a href="https://github.com/sarangop1728/7-adic-settlers-of-cartan">Code</a></p>
</nav>
<button class="ec-menu" type="button" aria-controls="ec-sidebar" aria-expanded="false">Contents</button>
</div>
<div id="content" class="content">
<h1 class="title" id="top">%(title)s</h1>
<p class="paper-authors">%(authors)s</p>
%(body)s
%(footnotes)s
</div>
</body>
</html>
""" % {"plain": html.escape(plain_title), "title": title, "authors": " and ".join(authors),
       "toc": "\n".join(toc), "body": body, "footnotes": footnotes}


def main(argv):
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("org")
    p.add_argument("aux")
    p.add_argument("outdir")
    p.add_argument("--code", default="build/code")
    p.add_argument("--out", default="build/out")
    p.add_argument("--cache", default="build/figures")
    a = p.parse_args(argv)

    stream, origin = read_org(a.org)
    begin = stream.index("\\begin{document}")
    preamble = stream[:begin]
    opening = preamble.find("% OPENING")
    figure_preamble = re.sub(r"\\documentclass(\[[^\]]*\])?\{[^}]+\}", "", preamble[:opening])
    body_start = begin + len("\\begin{document}")
    body_end = stream.index("\\end{document}")
    os.makedirs(a.outdir, exist_ok=True)
    conv = Converter(stream, origin, read_aux(a.aux), a.code, a.out, a.cache,
                     figure_preamble, a.outdir)
    try:
        title, authors = front_matter(conv, preamble)
        body = "\n".join(conv.blocks(stream[body_start:body_end], body_start))
        # web-only material after \end{document} (the code infrastructure)
        after = body_end + len("\\end{document}")
        body += "\n" + "\n".join(conv.blocks(stream[after:], after))
    except ConversionError as e:
        sys.exit("tex2html: %s" % e)
    import unicodedata
    with open(os.path.join(a.outdir, "index.html"), "w", encoding="utf-8") as f:
        f.write(unicodedata.normalize("NFC", page(conv, title, authors, body)))
    with open(os.path.join(a.outdir, "macros.js"), "w", encoding="utf-8") as f:
        f.write(macros_js(preamble))
    here = os.path.dirname(os.path.abspath(__file__))
    for asset in ("org-css.css", "org-code.js", "book.css", "book.js", "paper.css"):
        shutil.copy(os.path.join(here, "assets", asset), os.path.join(a.outdir, asset))
    print("tex2html: %s/index.html, %d sections, %d Magma boxes"
          % (a.outdir, len(conv.sections), len(conv.magma_seen)))


if __name__ == "__main__":
    main(sys.argv[1:])
