#!/usr/bin/env python3
"""Split the reports of the Magma files into one snippet per statement.

Usage:  tools/split-output.py OUTDIR REPORT...

A report is the output of one magma/*.m file.  Each statement in it starts
with a header printed by the procedure `statement' of the org file:

    ------------------------------------------------------------------------
    Lemma 2.1  the arithmetic of the forms   [lem:arithmetic-of-forms]
    ------------------------------------------------------------------------

and runs to the next header, or to the closing line of the file.  The lines
in between go to OUTDIR/<label>.txt, where tools/tex2html.py finds them.
"""

import os
import re
import sys

RULE = re.compile(r"^-{20,}$")
HEADER = re.compile(r"^(.+?)   \[([^\]]+)\]$")
CLOSING = re.compile(r"^\S+\.m: every check passed")


def split(report):
    lines = open(report, encoding="utf-8").read().split("\n")
    snippets, label, body = {}, None, []
    i = 0
    while i < len(lines):
        if (RULE.match(lines[i]) and i + 2 < len(lines)
                and HEADER.match(lines[i + 1]) and RULE.match(lines[i + 2])):
            if label:
                snippets[label] = body
            label, body = HEADER.match(lines[i + 1]).group(2), []
            i += 3
            continue
        if CLOSING.match(lines[i]):
            break
        if label:
            body.append(lines[i])
        i += 1
    if label:
        snippets[label] = body
    return snippets


def main(argv):
    outdir, reports = argv[0], argv[1:]
    os.makedirs(outdir, exist_ok=True)
    count = 0
    for report in reports:
        text = open(report, encoding="utf-8").read()
        if not re.search(r"^\S+\.m: every check passed", text, re.M):
            sys.exit("split-output: %s did not finish; rerun it before building the page" % report)
        for label, body in split(report).items():
            while body and not body[-1].strip():
                body.pop()
            with open(os.path.join(outdir, label + ".txt"), "w", encoding="utf-8") as f:
                f.write("\n".join(body) + "\n")
            count += 1
    print("split-output: %d snippets in %s" % (count, outdir))


if __name__ == "__main__":
    main(sys.argv[1:])
