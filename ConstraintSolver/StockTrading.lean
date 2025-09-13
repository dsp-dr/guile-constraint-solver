import ConstraintSolver.Basic

namespace ConstraintSolver.StockTrading

/-- Find maximum profit from buying and selling once -/
def maxProfit (prices : List Nat) : Nat × (Nat × Nat) :=
  match prices with
  | [] => (0, (0, 0))
  | p :: ps =>
    let rec loop (rest : List Nat) (idx : Nat) (minPrice : Nat) (minIdx : Nat)
                 (maxProfit : Nat) (bestBuy : Nat) (bestSell : Nat) :=
      match rest with
      | [] => (maxProfit, (bestBuy, bestSell))
      | price :: rest' =>
        let profit := if price > minPrice then price - minPrice else 0
        if profit > maxProfit then
          loop rest' (idx + 1) (min minPrice price)
               (if price < minPrice then idx else minIdx)
               profit minIdx idx
        else if price < minPrice then
          loop rest' (idx + 1) price idx maxProfit bestBuy bestSell
        else
          loop rest' (idx + 1) minPrice minIdx maxProfit bestBuy bestSell
    loop ps 1 p 0 0 0 0

/-- Property: Buy happens before sell -/
theorem maxProfit_buy_before_sell (prices : List Nat) :
  let (_, (buy, sell)) := maxProfit prices
  prices.length > 1 → buy < sell := by
  sorry

/-- Extended version with transaction limits -/
structure TradingConstraints where
  maxTransactions : Nat
  holdingLimit : Nat
  deriving Repr

/-- State for dynamic programming -/
structure TradingState where
  day : Nat
  transactions : Nat
  holding : Nat
  profit : Int
  deriving Repr, BEq

/-- Example with article's data -/
def examplePrices : List Nat := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8]

#eval maxProfit examplePrices

/-- Verify specific solution using omega -/
example : ∃ (buy sell : Nat),
  buy < sell ∧
  buy < examplePrices.length ∧
  sell < examplePrices.length ∧
  (examplePrices.get? sell).getD 0 - (examplePrices.get? buy).getD 0 = 8 := by
  use 1, 5  -- Buy at index 1 (price 1), sell at index 5 (price 9)
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · simp [examplePrices]
    omega

end ConstraintSolver.StockTrading
