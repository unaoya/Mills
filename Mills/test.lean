import Init.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

example (x : ℝ) (xpos : 0 ≤ x) : (Nat.cast : ℕ → ℤ) (Nat.floor x) = Int.floor x := by
  symm
  rw [Int.floor_eq_iff]
  constructor
  · simp
    apply Nat.floor_le xpos
  · simp
    apply Nat.lt_floor_add_one
