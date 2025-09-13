.PHONY: all setup test examples clean tutorial setup-lean4

all: setup

setup:
	sh scripts/create-structure.sh
	sh scripts/install-deps.sh

setup-lean4:
	sh scripts/install-lean4.sh

test:
	guile -L ./src tests/unit/test-change-making.scm
	guile -L ./src tests/unit/test-n-queens.scm

examples:
	guile -L ./src ./examples/run-examples.scm

tutorial:
	guile -L ./src ./examples/tutorials/basic-csp.scm

graph-coloring:
	guile -L ./src ./examples/leetcode/graph-coloring.scm

clean:
	find . -name "*.go" -delete
	find . -name "*~" -delete

tangle:
	emacs --batch -l org --eval "(org-babel-tangle-file \"setup.org\")"
