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

import Mills.Defs

open Filter Topology NNReal

example (x : ℝ) (xpos : 0 < x) : x ^ 3 + x ^ 2 ≤ (x + 1) ^ 3 - 1 := by nlinarith

-- 定理3の冒頭の不等式。これは一般的に成り立つ。似た話を後でも使う？
lemma aux_ineq_in_thm3 (x : ℝ≥0) (xgt1 : 1 < x.val) : x.rpow 3 + x.rpow (3 * θ).toReal < (x + 1).rpow 3 - 1 := by
  have h₀ : (3 * θ).toReal < 2 := by rw [θ]; norm_num;
  have h₁ : x.rpow 3 + x.rpow (3 * θ).toReal < x.rpow 3 + x.rpow 2 := by
      apply add_lt_add_left
      apply Real.rpow_lt_rpow_of_exponent_lt xgt1 h₀
  have h₂ (x : ℝ) (h : 1 < x) : x ^ 3 + x ^ 2 < (x + 1) ^ 3 - 1 := by nlinarith
  have h₃ : x.rpow 3 + x.rpow (3 * θ).toReal < (x + 1).rpow 3 - 1 := by sorry
  exact h₃
