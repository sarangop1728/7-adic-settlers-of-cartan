#!/usr/bin/env python3
"""Copy the Overleaf version of the paper into the LaTeX blocks of the org file.

Usage:  tools/sync-from-overleaf.py ORG TEX [--dry-run]

The paper is edited on Overleaf.  This script cuts TEX into pieces, one per
LaTeX block of ORG that tangles to the paper, and replaces each block's body
by its piece; everything else in ORG (headings, prose, Magma blocks) is left
alone.  Tangling ORG afterwards gives back TEX byte for byte.

The cut points are the first lines of the existing blocks: each block's piece
starts at the first line of TEX, after the previous block's start, that equals
the block's current first line.  Org-babel strips the blank lines at the ends
of a block and puts one blank line between consecutive blocks, so each cut
point must be preceded by exactly one blank line, and TEX must not end with a
blank line.  The script stops, changing nothing, if a first line is missing
from TEX or a cut point breaks that rule; it lists the blocks whose content
changed, and the \\label's that a block gained or lost, so that a new
statement can be given a heading and a block of its own by hand.
"""

import re
import sys


def blocks(lines):
    """The LaTeX blocks of the org file that tangle to the paper:
    (index of the #+begin_src line, index of the #+end_src line)."""
    out = []
    i = 0
    while i < len(lines):
        m = re.match(r"\s*#\+begin_src\s+(\S+)(.*)", lines[i], re.I)
        if m:
            j = i + 1
            while not re.match(r"\s*#\+end_src", lines[j], re.I):
                j += 1
            if m.group(1) == "latex" and ":tangle no" not in m.group(2):
                out.append((i, j))
            i = j + 1
            continue
        i += 1
    return out


def unescape(line):
    return re.sub(r"^(\s*),(\*|#\+|,\*|,#\+)", r"\1\2", line)


def escape(line):
    return re.sub(r"^(\s*)(\*|#\+|,\*|,#\+)", r"\1,\2", line)


def main(argv):
    dry = "--dry-run" in argv
    argv = [a for a in argv if a != "--dry-run"]
    org_path, tex_path = argv
    org = open(org_path, encoding="utf-8").read().split("\n")
    tex = open(tex_path, encoding="utf-8").read()
    if not tex.endswith("\n") or tex.endswith("\n\n"):
        sys.exit("sync: %s must end with exactly one newline" % tex_path)
    tex_lines = tex[:-1].split("\n")

    spans = blocks(org)
    firsts = [unescape(org[b + 1]) for b, _ in spans]
    cuts, pos = [], 0
    for k, first in enumerate(firsts):
        while pos < len(tex_lines) and tex_lines[pos] != first:
            pos += 1
        if pos == len(tex_lines):
            sys.exit("sync: the first line of LaTeX block %d is no longer in the paper:\n    %s\n"
                     "Edit that block's first line in the org file to the new text, then rerun."
                     % (k + 1, first))
        if k > 0 and not (tex_lines[pos - 1] == "" and tex_lines[pos - 2] != ""):
            sys.exit("sync: line %d of the paper starts a block, so exactly one blank line must precede it:\n    %s"
                     % (pos + 1, first))
        if k == 0 and pos != 0:
            sys.exit("sync: the paper must start with the first line of the first block")
        cuts.append(pos)
        pos += 1

    pieces = []
    for k, start in enumerate(cuts):
        end = cuts[k + 1] - 1 if k + 1 < len(cuts) else len(tex_lines)
        piece = tex_lines[start:end]
        if piece and piece[-1] == "" and k + 1 == len(cuts):
            sys.exit("sync: the paper ends with a blank line")
        pieces.append(piece)

    labels = lambda ls: set(re.findall(r"\\label\{([^}]+)\}", "\n".join(ls)))
    new_org, last, changed = [], 0, []
    for k, ((b, e), piece) in enumerate(zip(spans, pieces)):
        old = [unescape(l) for l in org[b + 1:e]]
        if old != piece:
            gained, lost = labels(piece) - labels(old), labels(old) - labels(piece)
            note = ""
            if gained:
                note += " gained " + ", ".join(sorted(gained))
            if lost:
                note += " lost " + ", ".join(sorted(lost))
            changed.append("block %d (%s): %d -> %d lines%s" % (k + 1, piece[0][:50], len(old), len(piece), note))
        new_org += org[last:b + 1] + [escape(l) for l in piece]
        last = e
    new_org += org[last:]

    if changed:
        print("sync: %d of %d blocks changed:" % (len(changed), len(spans)))
        for c in changed:
            print("  " + c)
    else:
        print("sync: the %d LaTeX blocks already match the paper" % len(spans))
    if changed and not dry:
        with open(org_path, "w", encoding="utf-8") as f:
            f.write("\n".join(new_org))


if __name__ == "__main__":
    main(sys.argv[1:])
