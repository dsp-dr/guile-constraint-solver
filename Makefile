# Guile Constraint Solver - GNU Make Best Practices
# Variables
GUILE := guile3
GUILE_FLAGS := -L ./src
EMACS := emacs
TEST_DIR := tests/unit
EXAMPLE_DIR := tests/examples
SRC_DIR := src
BUILD_DIR := .build

# Sentinel files for idempotent operations
SETUP_SENTINEL := $(BUILD_DIR)/.setup-done
STRUCTURE_SENTINEL := $(BUILD_DIR)/.structure-created
DEPS_SENTINEL := $(BUILD_DIR)/.deps-installed
LEAN4_SENTINEL := $(BUILD_DIR)/.lean4-installed

# Default target - show help
.DEFAULT_GOAL := help

# Phony targets
.PHONY: help all setup setup-lean4 test examples tutorial graph-coloring clean distclean tangle
.PHONY: lean-build lean-run lean-verify lean-all compare

help: ## Show this help message
	@echo "Guile Constraint Solver - Available targets:"
	@echo
	@grep -E '^[a-zA-Z_-]+:.*## .*$$' $(MAKEFILE_LIST) | \
		awk 'BEGIN {FS = ":.*## "}; {printf "  \033[36m%-15s\033[0m %s\n", $$1, $$2}'
	@echo
	@echo "Sentinel files track completion to ensure idempotent operations"

all: $(SETUP_SENTINEL) ## Complete project setup

# Setup with sentinel-based idempotency
$(SETUP_SENTINEL): $(STRUCTURE_SENTINEL) $(DEPS_SENTINEL)
	@echo "==> Setup complete"
	@touch $@

$(STRUCTURE_SENTINEL): scripts/create-structure.sh | $(BUILD_DIR)
	@echo "==> Creating project structure..."
	@sh $<
	@touch $@

$(DEPS_SENTINEL): scripts/install-deps.sh | $(BUILD_DIR)
	@echo "==> Installing dependencies..."
	@sh $<
	@touch $@

$(LEAN4_SENTINEL): scripts/install-lean4.sh | $(BUILD_DIR)
	@echo "==> Installing Lean 4..."
	@sh $<
	@touch $@

$(BUILD_DIR):
	@mkdir -p $@

# Aliases for common operations
setup: $(SETUP_SENTINEL) ## Run basic project setup

setup-lean4: $(LEAN4_SENTINEL) ## Install Lean 4 theorem prover

# Testing with pattern rules and automatic variables
TEST_SOURCES := $(wildcard $(TEST_DIR)/test-*.scm)
TEST_TARGETS := $(TEST_SOURCES:$(TEST_DIR)/test-%.scm=$(BUILD_DIR)/test-%.done)

test: $(TEST_TARGETS) ## Run all unit tests
	@echo "==> All tests completed successfully"

$(BUILD_DIR)/test-%.done: $(TEST_DIR)/test-%.scm $(SETUP_SENTINEL) | $(BUILD_DIR)
	@echo "==> Running test: $*"
	@$(GUILE) $(GUILE_FLAGS) $<
	@touch $@

# Example execution
EXAMPLE_SOURCES := $(wildcard $(EXAMPLE_DIR)/*.scm $(EXAMPLE_DIR)/*/*.scm)
EXAMPLE_TARGETS := $(EXAMPLE_SOURCES:%.scm=$(BUILD_DIR)/%.done)

examples: $(BUILD_DIR)/$(EXAMPLE_DIR)/run-examples.done ## Run main examples

tutorial: $(BUILD_DIR)/$(EXAMPLE_DIR)/tutorials/basic-csp.done ## Run tutorial

graph-coloring: $(BUILD_DIR)/$(EXAMPLE_DIR)/leetcode/graph-coloring.done ## Run graph coloring example

$(BUILD_DIR)/%.done: %.scm $(SETUP_SENTINEL) | $(BUILD_DIR)
	@echo "==> Running example: $<"
	@mkdir -p $(dir $@)
	@$(GUILE) $(GUILE_FLAGS) $<
	@touch $@

# Org-mode tangling with dependency tracking
TANGLED_FILES := $(shell grep -o ':tangle [^[:space:]]*' setup.org 2>/dev/null | cut -d' ' -f2)

tangle: $(TANGLED_FILES) ## Tangle org-mode files

$(TANGLED_FILES): setup.org
	@echo "==> Tangling $@ from $<"
	@$(EMACS) --batch -l org --eval "(org-babel-tangle-file \"$<\")"

# Cleaning with proper dependency order
clean: ## Clean build artifacts and compiled files
	@echo "==> Cleaning build artifacts..."
	@rm -rf $(BUILD_DIR)
	@find . -name "*.go" -delete 2>/dev/null || true
	@find . -name "*~" -delete 2>/dev/null || true
	@find . -name ".#*" -delete 2>/dev/null || true
	@find . -name "\#*\#" -delete 2>/dev/null || true

distclean: clean ## Deep clean including sentinel files and caches
	@echo "==> Deep cleaning..."
	@rm -rf .cache
	@find . -name "core" -delete 2>/dev/null || true
	@find . -name "core.*" -delete 2>/dev/null || true
	@find . -name "vgcore.*" -delete 2>/dev/null || true

# Lean4 integration
LEAN4_BUILD_SENTINEL := $(BUILD_DIR)/.lean4-built
LAKE := lake

lean-build: $(LEAN4_BUILD_SENTINEL) ## Build Lean4 constraint solver

$(LEAN4_BUILD_SENTINEL): lakefile.toml $(wildcard ConstraintSolver/*.lean) | $(BUILD_DIR)
	@echo "==> Building Lean4 project..."
	@$(LAKE) build
	@touch $@

lean-run: $(LEAN4_BUILD_SENTINEL) ## Run Lean4 examples
	@echo "==> Running Lean4 examples..."
	@$(LAKE) exe examples

lean-verify: $(LEAN4_BUILD_SENTINEL) ## Verify Lean4 proofs
	@echo "==> Verifying Lean4 proofs..."
	@$(LAKE) env lean ConstraintSolver/Verification.lean

lean-all: lean-build lean-run lean-verify ## Run all Lean4 tasks

compare: examples lean-run ## Compare Guile and Lean4 solutions
	@echo "==> Comparing solutions..."
	@chmod +x scripts/compare-solutions.scm
	@./scripts/compare-solutions.scm

# Debug target to show variables
debug: ## Show Makefile variables for debugging
	@echo "GUILE: $(GUILE)"
	@echo "GUILE_FLAGS: $(GUILE_FLAGS)"
	@echo "BUILD_DIR: $(BUILD_DIR)"
	@echo "TEST_SOURCES: $(TEST_SOURCES)"
	@echo "TEST_TARGETS: $(TEST_TARGETS)"
	@echo "EXAMPLE_SOURCES: $(EXAMPLE_SOURCES)"
	@echo "TANGLED_FILES: $(TANGLED_FILES)"
	@echo "LAKE: $(LAKE)"