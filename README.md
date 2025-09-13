# Guile Constraint Solver

Constraint solving approaches in Guile Scheme, inspired by Hillel Wayne's
"Many Hard Leetcode Problems are Easy Constraint Problems" article.

## Features

- Native Guile constraint propagation engine with backtracking
- Z3 SMT solver integration via SMT-LIB2
- Example implementations of classic constraint problems:
  - Coin change problem (DP + CSP + Z3)
  - N-Queens problem (CSP + Z3)
  - Sudoku solver (CSP + Z3)
  - Graph coloring (CSP + Z3)
- Performance comparison between different solving approaches

## Installation

On FreeBSD:

```bash
# Clone the repository
git clone https://github.com/dsp-dr/guile-constraint-solver.git
cd guile-constraint-solver

# Run setup (installs dependencies and creates structure)
make setup
```

## Usage

```scheme
;; Coin change problem
(use-modules (problems change-making))
(make-change-dp 37 '(10 9 1))  ; => (10 9 9 9)

;; N-Queens problem
(use-modules (problems n-queens))
(n-queens-csp 4)  ; => Solution for 4x4 board

;; Graph coloring
(use-modules (problems graph-coloring))
(graph-coloring-csp graph 5 3)  ; => 3-color solution
```

## Examples

```bash
# Run basic tutorial
make tutorial

# Run all examples
make examples

# Graph coloring demo
make graph-coloring
```

## Testing

```bash
make test
```

## Project Structure

```
src/
├── core/constraint-engine.scm    # Native CSP solver
├── z3/interface.scm              # Z3 SMT integration
└── problems/                     # Problem implementations
    ├── change-making.scm
    ├── n-queens.scm
    ├── sudoku.scm
    └── graph-coloring.scm
examples/
├── tutorials/basic-csp.scm       # Tutorial walkthrough
└── leetcode/graph-coloring.scm   # LeetCode-style problems
tests/
└── unit/                         # Unit tests
```

## License

MIT License
