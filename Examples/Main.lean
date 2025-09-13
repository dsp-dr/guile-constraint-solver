import ConstraintSolver.ChangeMaking
import ConstraintSolver.StockTrading
import ConstraintSolver.ThreeSum
import ConstraintSolver.Histogram

def main : IO Unit := do
  IO.println "=== Lean4 Constraint Solving Examples ==="

  -- Change Making
  IO.println "\n1. Change Making (37 cents with [10, 9, 1]):"
  match ConstraintSolver.ChangeMaking.makeChange 37 [10, 9, 1] with
  | some solution => IO.println s!"   Solution: {solution}"
  | none => IO.println "   No solution found"

  -- Stock Trading
  IO.println "\n2. Stock Trading:"
  let prices := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8]
  let (profit, (buy, sell)) := ConstraintSolver.StockTrading.maxProfit prices
  IO.println s!"   Prices: {prices}"
  IO.println s!"   Max profit: {profit} (buy at index {buy}, sell at {sell})"

  -- Three Sum
  IO.println "\n3. Three Sum:"
  let numbers := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8]
  match ConstraintSolver.ThreeSum.findThreeSum numbers with
  | some (i, j, k, si, sj, sk) =>
    IO.println s!"   Numbers: {numbers}"
    IO.println s!"   Solution: {numbers[i]!}*{si} + {numbers[j]!}*{sj} + {numbers[k]!}*{sk} = 0"
  | none => IO.println "   No solution found"

  -- Histogram
  IO.println "\n4. Largest Rectangle in Histogram:"
  let heights := [2, 1, 5, 6, 2, 3]
  let rect := ConstraintSolver.Histogram.largestRectangle heights
  IO.println s!"   Heights: {heights}"
  IO.println s!"   Largest rectangle: start={rect.start}, width={rect.width}, height={rect.height}, area={rect.area}"
