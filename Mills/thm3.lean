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
  have h₃ : x.rpow 3 + x.rpow (3 * θ).toReal < (x + 1).rpow 3 - 1 := by
    calc
      x.rpow 3 + x.rpow (3 * θ).toReal < x.rpow 3 + x.rpow 2 := by
        apply add_lt_add_left
        dsimp [rpow]
        apply Real.rpow_lt_rpow_of_exponent_lt xgt1
        simp at h₀
        exact h₀
      _ ≤ x.rpow 3 + 3 * x.rpow 2 := by
        apply add_le_add_left
        rw [le_mul_iff_one_le_left]
        norm_num
        dsimp [rpow]
        rw [← NNReal.coe_lt_coe]
        simp
        have : x.val = toReal x := by simp
        nlinarith
      _ ≤ x.rpow 3 + 3 * x.rpow 2 + 3 * x.rpow 1 := by apply le_add_of_nonneg_right (by simp)
      _ = (x + 1).rpow 3 - 1 := by
        dsimp [Real.rpow]
        rw [← NNReal.eq_iff]
        simp
        ring_nf
        rw [add_assoc 1, add_assoc 1, add_tsub_cancel_left]
        simp
  exact h₃

theorem exists_Mills : ∃ A : ℝ≥0, Mills A := by sorry
/-
  have : 1 < pp 1 := by rw [pp]; linarith [(pp' 1).property, BHP_const_nat_ge2]
  use (left_lim pp)
  constructor
  · exact (by linarith [(left_gt_1 pp this), (left_le_sup pp (fun n ↦(hpp n).right.right.left) 1)])
  · intro k h
    rw [left_floor_eq_seq pp (fun n ↦ (hpp n).left) (fun n ↦ (hpp n).right.right.left) k, ← Nat.succ_pred_eq_of_pos h]
    exact (hpp k.pred).right.right.right
-/

theorem W_nonempty : W.Nonempty := exists_Mills
