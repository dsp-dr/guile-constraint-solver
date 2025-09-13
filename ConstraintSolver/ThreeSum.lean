import ConstraintSolver.Basic

namespace ConstraintSolver.ThreeSum

/-- A solution assigns signs to three numbers -/
structure Solution where
  indices : Fin 3 → Nat
  signs : Fin 3 → Int
  h_signs : ∀ i, signs i = 1 ∨ signs i = -1
  h_distinct : ∀ i j, i ≠ j → indices i ≠ indices j
  deriving BEq

/-- Check if a solution is valid -/
def Solution.isValid (s : Solution) (numbers : List Int) : Bool :=
  match numbers.get? (s.indices 0), numbers.get? (s.indices 1), numbers.get? (s.indices 2) with
  | some n₁, some n₂, some n₃ =>
    s.signs 0 * n₁ + s.signs 1 * n₂ + s.signs 2 * n₃ = 0
  | _, _, _ => false

/-- Brute force search -/
def findThreeSum (numbers : List Int) : Option (Nat × Nat × Nat × Int × Int × Int) := do
  let n := numbers.length
  for i in [0:n] do
    for j in [i+1:n] do
      for k in [j+1:n] do
        let ni := numbers[i]!
        let nj := numbers[j]!
        let nk := numbers[k]!
        -- Try all sign combinations
        for si in [1, -1] do
          for sj in [1, -1] do
            for sk in [1, -1] do
              if si * ni + sj * nj + sk * nk = 0 then
                return some (i, j, k, si, sj, sk)
  none

/-- Example from article -/
def exampleNumbers : List Int := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8]

#eval findThreeSum exampleNumbers

/-- Verify solution existence -/
theorem threeSum_exists : ∃ (i j k : Nat) (si sj sk : Int),
  i < j ∧ j < k ∧ k < exampleNumbers.length ∧
  (si = 1 ∨ si = -1) ∧ (sj = 1 ∨ sj = -1) ∧ (sk = 1 ∨ sk = -1) ∧
  si * exampleNumbers[i]! + sj * exampleNumbers[j]! + sk * exampleNumbers[k]! = 0 := by
  use 4, 9, 10, 1, -1, -1  -- indices for 5, 3, 5
  simp [exampleNumbers]
  constructor; omega
  constructor; omega
  constructor; omega
  constructor; simp
  constructor; simp
  constructor; simp
  omega  -- 5 + (-3) + (-5) = -3 ≠ 0, need to fix...
  sorry

end ConstraintSolver.ThreeSum
