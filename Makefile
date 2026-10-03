# 7-adic-settlers-of-cartan: one org file, three outputs.
#
#   make tangle      7-adic-settlers.tex and magma/*.m, from the org file
#   make pdf         build/7-adic-settlers.pdf; fails on undefined references or citations
#   make check       run the six Magma files (in parallel with make -j), and check the
#                    statement numbers they print against the paper
#   make html        the web version, docs/index.html (GitHub Pages serves docs/)
#   make all         all of the above
#   make sync        copy the Overleaf version of the paper into the org file
#   make check-sync  the tangled paper is byte-identical to the Overleaf version
#   make clean       remove build/
#
# Only 7-adic-settlers-of-cartan.org and tools/ are edited by hand.

ORG      = 7-adic-settlers-of-cartan.org
TEX      = 7-adic-settlers.tex
NAMES    = descent equations kummer klein theorem-1 theorem-2
MAGMAS   = $(NAMES:%=magma/%.m)
REPORTS  = $(NAMES:%=build/reports/%.txt)
OVERLEAF ?= ../overleaf/7-adic-settlers.tex

EMACS   ?= emacs
MAGMA   ?= magma
PYTHON  ?= python3
LATEXMK  = latexmk -pdf -interaction=nonstopmode -halt-on-error

.PHONY: all tangle pdf check html sync check-sync clean

all: tangle pdf check html

# org-src-preserve-indentation: the paper's indentation must survive tangling.
tangle: build/tangle.stamp
build/tangle.stamp: $(ORG)
	@mkdir -p build magma
	$(EMACS) --batch -Q --eval '(progn (require (quote ob-tangle)) (setq org-src-preserve-indentation t) (org-babel-tangle-file "$(ORG)"))'
	@touch $@

pdf: build/7-adic-settlers.pdf
build/7-adic-settlers.pdf: build/tangle.stamp
	cp $(TEX) build/
	cd build && $(LATEXMK) $(TEX)
	@# latexmk succeeds on undefined references; the paper must not.
	@if grep -E 'There were undefined references|Reference .* undefined|Citation .* undefined' build/7-adic-settlers.log; then \
	  echo "ERROR: undefined references in build/7-adic-settlers.pdf"; rm -f $@; exit 1; fi

# Each Magma file runs on its own, from build/reports/, and must exit 0.
check: $(REPORTS) build/7-adic-settlers.pdf
	$(PYTHON) tools/check-numbers.py build/7-adic-settlers.aux $(MAGMAS)

build/reports/%.txt: build/tangle.stamp
	@mkdir -p build/reports
	cd build/reports && $(MAGMA) -b ../../magma/$*.m < /dev/null > $*.tmp 2>&1 \
	  || { cat $*.tmp; echo "ERROR: magma/$*.m failed"; exit 1; }
	@mv build/reports/$*.tmp $@
	@tail -1 $@

html: docs/index.html
docs/index.html: build/tangle.stamp build/7-adic-settlers.pdf $(REPORTS) tools/tex2html.py tools/export-code.el tools/assets/paper.css
	$(EMACS) --batch -Q -l tools/export-code.el -f paper/export-code $(ORG) build/code
	$(PYTHON) tools/split-output.py build/snippets $(REPORTS)
	$(PYTHON) tools/tex2html.py $(ORG) build/7-adic-settlers.aux docs \
	  --code build/code --out build/snippets --cache build/figures
	@mkdir -p docs/magma
	cp $(MAGMAS) docs/magma/
	cp build/7-adic-settlers.pdf docs/

sync:
	$(PYTHON) tools/sync-from-overleaf.py $(ORG) $(OVERLEAF)

check-sync: build/tangle.stamp
	cmp $(TEX) $(OVERLEAF) && echo "check-sync: $(TEX) is identical to $(OVERLEAF)"

clean:
	rm -rf build
