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

open NNReal

-- 補題6はミルズ定数でなく、一般のミルズ数についても成り立つ？
-- 最小性を使わない？（が実際の証明ではミルズ定数の場合しか使わない。）

#print Int.add_one_le_iff
#print Int.lt_add_one_iff

/-
lemma lem6 (k : ℕ+) (x : ℝ≥0) (xm : Mills x) : (Mills_seq x k) ^ 3 ≤ (Mills_seq x (k + 1)) ∧ (Mills_seq x (k + 1)) < (Mills_seq x k + 1) ^ 3 - 1 := by
  have h₀ : Mills_seq x k ≤ x.rpow (3 ^ k) ∧ x.rpow (3 ^ k) < Mills_seq x k + 1 := by sorry
  have h₁ : (Mills_seq x k) ^ 3 ≤ x.rpow (3 ^ (k + 1)) ∧ x.rpow (3 ^ (k + 1)) < (Mills_seq x k + 1) ^ 3 := by sorry
  have h₂ : Mills_seq x (k + 1) = Nat.floor (x.rpow (3 ^ (k + 1))) := by sorry
  have h₃ : Mills_seq x (k + 1) ≤ (Mills_seq x k + 1) ^ 3 - 1:= by sorry
  have h₄ : Mills_seq x (k + 1) ≠ (Mills_seq x k + 1) ^ 3 - 1 := by
    intro h
    apply not_prime (Mills_seq x k) (Mills_seq_ge_2 x k xm)
    rw [← h]
    exact xm.right (k + 1)
  constructor
  · sorry
  · exact lt_of_le_of_ne h₃ h₄
-/
