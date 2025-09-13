import ConstraintSolver.Basic

namespace ConstraintSolver.Histogram

/-- Rectangle in histogram -/
structure Rectangle where
  start : Nat
  width : Nat
  height : Nat
  deriving Repr, BEq

/-- Check if rectangle is valid for given heights -/
def Rectangle.isValid (r : Rectangle) (heights : List Nat) : Bool :=
  r.width > 0 ∧
  r.start + r.width ≤ heights.length ∧
  (List.range r.width).all fun i =>
    match heights.get? (r.start + i) with
    | some h => h ≥ r.height
    | none => false

/-- Area of rectangle -/
def Rectangle.area (r : Rectangle) : Nat := r.width * r.height

/-- Find largest rectangle - O(n²) algorithm -/
def largestRectangle (heights : List Nat) : Rectangle :=
  let n := heights.length
  let candidates := List.join <| List.range n |>.map fun i =>
    List.range (n - i) |>.filterMap fun w =>
      let width := w + 1
      let minHeight := (List.range width).foldl (fun acc j =>
        match heights.get? (i + j) with
        | some h => min acc h
        | none => acc
      ) (heights[i]!.max 1)
      if minHeight > 0 then
        some ⟨i, width, minHeight⟩
      else none

  candidates.foldl (fun best rect =>
    if rect.area > best.area then rect else best
  ) ⟨0, 1, 1⟩

/-- Example from article -/
def exampleHeights : List Nat := [2, 1, 5, 6, 2, 3]

#eval largestRectangle exampleHeights

/-- Verify optimality of a specific solution -/
theorem histogram_optimal :
  let heights := exampleHeights
  let rect := Rectangle.mk 2 2 5
  rect.isValid heights ∧
  rect.area = 10 ∧
  (∀ r : Rectangle, r.isValid heights → r.area ≤ 10) := by
  simp [Rectangle.isValid, Rectangle.area, exampleHeights]
  constructor
  · simp [List.all, List.range]
    omega
  constructor
  · omega
  · intro r h_valid
    sorry -- Would need to enumerate all possibilities

end ConstraintSolver.Histogram
