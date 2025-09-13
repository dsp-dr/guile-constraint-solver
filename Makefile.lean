# Lean4 specific targets
.PHONY: lean-build lean-run lean-verify lean-all

lean-build:
	lake build

lean-run: lean-build
	lake exe examples

lean-verify:
	lake env lean ConstraintSolver/Verification.lean

lean-all: lean-build lean-run

compare: examples lean-run
	./scripts/compare-solutions.scm
