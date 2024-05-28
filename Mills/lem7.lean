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

lemma xgt1_ne_0 (x : ℝ≥0) (h : 1 < x) : x ≠ 0 := by
  rw [← NNReal.coe_ne_zero]
  rw [← NNReal.one_lt_coe] at h
  linarith

-- どっかで似たようなことをやってる
lemma aux_ineq_in_lem7_2 (x : ℝ≥0) (xgt1 : 1 < x) : x.rpow 3 + x.rpow (3 * θ) + 1 ≤ x.rpow 3 * (1 + 2 * x.rpow (3 * (θ - 1))) := by
  ring_nf
  rw [add_comm 1 _, add_assoc]
  apply add_le_add_left _ (x.rpow 3)
  simp
  rw [NNReal.rpow_add, ← mul_assoc, ← NNReal.rpow_natCast, ← NNReal.rpow_add]
  simp
  rw [mul_two]
  apply add_le_add_right
  apply NNReal.one_le_rpow (le_of_lt xgt1) (by norm_num)
  exact xgt1_ne_0 x xgt1
  exact xgt1_ne_0 x xgt1


-- 型をどうするか？冪乗、aはℝ≥0か？
lemma aux_ineq_in_lem7 (a : ℝ) (apos : 0 < a) : (1 + a) ^ ((1 : ℝ) / 3) ≤ a / 3 + 1 := by
  rw [← sub_le_iff_le_add]
  let f : ℝ → ℝ := fun x ↦ (1 + x) ^ ((1 : ℝ) / 3)
  let f' : ℝ → ℝ := fun x ↦ 1 * (1 / 3) * (1 + x) ^ ((1 : ℝ) / 3 - 1)
  have h : ContinuousOn f (Set.Icc 0 a) := ContinuousOn.rpow_const (Continuous.continuousOn (continuous_add_left 1)) (fun x _ ↦ Or.inr (by norm_num))
  have h' (x : ℝ) (hx : x ∈ Set.Ioo 0 a) : HasDerivAt f (f' x) x := by
    have hx' : (fun x ↦ 1 + x) x ≠ 0 ∨ (1 : ℝ) ≤ ((1 : ℝ) / 3) := by left; simp; linarith [hx.left]
    apply HasDerivAt.rpow_const (HasDerivAt.const_add 1 (hasDerivAt_id x)) hx'
  rcases (exists_hasDerivAt_eq_slope f f' apos h h') with ⟨c, hc₁, hc₂⟩
  calc
    (1 + a) ^ ((1 : ℝ) / 3) - 1 = f a - f 0 := by dsimp [f]; simp
    _ = f' c * a := by field_simp [hc₂]
    _ = (1 + c) ^ (-(2 : ℝ) / 3) * a / 3 := by dsimp [f']; ring_nf
    _ ≤ a / 3 := by
      rw [div_le_div_right (by norm_num), mul_le_iff_le_one_left apos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hc₁.left]) (by linarith)

-- k₁の条件は除いても強くなるはず（書き換えも形式化したほうがいい）
lemma lem7 : ∃ γ : ℝ≥0, γ > 0 ∧ ∃ k₁ : ℕ+, ∀ k, k₁ ≤ k → |(A.rpow (pnat_cube k)).val - (Mills_seq A k)| ≤ Real.exp (-γ * (pnat_cube k)) := by sorry
