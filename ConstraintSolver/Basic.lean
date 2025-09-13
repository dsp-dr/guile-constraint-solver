import Lean
import Std.Data.List.Basic
import Std.Data.Array.Basic

namespace ConstraintSolver

/-- Result type for constraint solving -/
inductive SolveResult (α : Type)
  | sat (solution : α) : SolveResult α
  | unsat : SolveResult α
  | timeout : SolveResult α
  deriving Repr, BEq

end ConstraintSolver
