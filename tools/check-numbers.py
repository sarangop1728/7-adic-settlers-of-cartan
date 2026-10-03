#!/usr/bin/env python3
"""Check the statement numbers that the Magma files print against the paper.

Usage:  tools/check-numbers.py AUX MAGMA-FILE...

Every statement block calls  statement("Lemma 2.1", "lem:arithmetic-of-forms", ...).
The first argument is what the reader sees in the report; the numbers in it are
typed by hand, so after the paper is edited they can go stale.  This script
reads LaTeX's own numbers from the .aux file of the compiled paper and checks:

  - the statement's label is in the paper, and the name contains its kind and
    number ("Lemma 2.1" for a lemma numbered 2.1, "(1.4)" for an equation);
  - every other piece of the name ("Theorem 1, (5.2)") names some statement,
    equation or section of the paper with that number.

Labels that are not in the paper (the steps of descent.m, "candidates-T") are
checked only for their other pieces.  Exits with status 1 on any mismatch.
"""

import re
import sys

KINDS = {
    "Lemma": {"lemma"}, "Proposition": {"proposition"}, "Corollary": {"corollary", "maincor"},
    "Remark": {"remark"}, "Example": {"example"}, "Definition": {"definition"},
    "Theorem": {"theorem", "mainthm"}, "Table": {"table"}, "Figure": {"figure"},
    "Section": {"section", "subsection"},
}


def read_aux(path):
    text = open(path, encoding="utf-8").read()
    entries = {}
    for m in re.finditer(r"\\newlabel\{([^}]+)@cref\}\{\{\[([^\]]*)\]\[[^\]]*\]\[[^\]]*\]([^}]*)\}", text):
        entries[m.group(1)] = (m.group(2), m.group(3))
    # sections without a \label are in the table of contents
    for m in re.finditer(r"\\contentsline \{(section|subsection)\}\{\\toc(?:sub)?section \{\}\{([0-9.]+)\}", text):
        entries["toc:%s" % m.group(2)] = (m.group(1), m.group(2))
    return entries


def piece_ok(piece, entries):
    piece = piece.strip()
    m = re.fullmatch(r"\((\d+\.\d+)\)", piece)
    if m:
        return any(kind == "equation" and num == m.group(1) for kind, num in entries.values())
    m = re.fullmatch(r"(\w+) (\d+(?:\.\d+)?)", piece)
    if m and m.group(1) in KINDS:
        return any(kind in KINDS[m.group(1)] and num == m.group(2) for kind, num in entries.values())
    if m and m.group(1) == "Step":
        return True
    return False


def label_piece(label, entries):
    kind, num = entries[label]
    if kind == "equation":
        return {"(%s)" % num}
    return {"%s %s" % (name, num) for name, kinds in KINDS.items() if kind in kinds}


def main(argv):
    entries = read_aux(argv[0])
    failures, count = [], 0
    for path in argv[1:]:
        source = open(path, encoding="utf-8").read()
        for m in re.finditer(r'statement\("([^"]+)", "([^"]+)"', source):
            name, label = m.group(1), m.group(2)
            count += 1
            pieces = [p.strip() for p in name.split(",")]
            for piece in pieces:
                if not piece_ok(piece, entries):
                    failures.append("%s: \"%s\" names nothing of that number in the paper" % (path, piece))
            if label in entries and not (label_piece(label, entries) & set(pieces)):
                failures.append("%s: \"%s\" for %s, which the paper numbers %s %s"
                                % (path, name, label, *entries[label]))
    for f in failures:
        print("check-numbers: " + f)
    if failures:
        sys.exit(1)
    print("check-numbers: the %d statement headers agree with the paper" % count)


if __name__ == "__main__":
    main(sys.argv[1:])
