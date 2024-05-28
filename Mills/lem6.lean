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

-- 補題として1より大きい自然数nに対して(n+1)^3-1が合成数となることを示しておく。
lemma not_prime (n : ℕ) (nge2 : 2 ≤ n) : ¬Nat.Prime ((n + 1) ^ 3 - 1) := by
  have h' : (n + 1) ^ 3 - 1 = n * (n ^ 2 + 3 * n + 3) := by
    ring_nf; rw [add_assoc, add_assoc, add_assoc, Nat.add_sub_self_left]
  rw [h']
  apply Nat.not_prime_mul (by linarith) (by simp)

lemma fl_cub_le_cub_fl (x : ℝ≥0) : (Nat.floor x) ^ 3 ≤ Nat.floor (x ^ 3) := by
  have : Nat.floor x ≤ x := by apply Nat.floor_le (by simp)
  have : (Nat.floor x) ^ 3 ≤ x ^ 3 := by apply pow_le_pow_left (by simp) this
  apply (Nat.le_floor_iff (by simp)).2
  simp
  exact this

lemma lem6 (k : ℕ+) (x : ℝ≥0) (xm : Mills x) : (Mills_seq x k) ^ 3 ≤ (Mills_seq x (k + 1)) ∧ (Mills_seq x (k + 1)) < (Mills_seq x k + 1) ^ 3 - 1 := by
  have h₀ : Mills_seq x k ≤ x.rpow (3 ^ k.val) ∧ x.rpow (3 ^ k.val) < Mills_seq x k + 1 := by
    dsimp [Mills_seq, pnpow]; simp
    exact ⟨Nat.floor_le (by simp), Nat.lt_floor_add_one _⟩
  have h₁ : (Mills_seq x k) ^ 3 ≤ x.rpow (3 ^ (k.val + 1)) ∧ x.rpow (3 ^ (k.val + 1)) < (Mills_seq x k + 1) ^ 3 := by
    dsimp [Mills_seq, pnpow] at *
    constructor
    · convert pow_le_pow_left (by simp) h₀.left 3
      rw [pow_succ, rpow_mul]
      simp
    · convert pow_lt_pow_left h₀.right (by simp) _
      rw [pow_succ, rpow_mul]
      simp
      simp
  have h₂ : Mills_seq x (k + 1) = Nat.floor (x.rpow (3 ^ (k.val + 1))) := by
    dsimp [Mills_seq, pnpow]
    simp
  have h₃ : Mills_seq x (k + 1) ≤ (Mills_seq x k + 1) ^ 3 - 1:= by
    have : Mills_seq x (k + 1) < (Mills_seq x k + 1) ^ 3 := by
      rw [h₂]
      rw [← @Nat.cast_lt ℝ≥0]
      simp
      calc
        ↑⌊x.rpow (3 ^ (↑k + 1))⌋₊ ≤ x.rpow (3 ^ (↑k + 1)) := by apply Nat.floor_le (by simp)
        _ < (Mills_seq x k + 1) ^ 3 := by apply h₁.right
    rw [← Nat.lt_iff_le_pred _]
    exact this
    simp
  have h₄ : Mills_seq x (k + 1) ≠ (Mills_seq x k + 1) ^ 3 - 1 := by
    intro h
    apply not_prime (Mills_seq x k) (Mills_seq_ge_2 x k xm)
    rw [← h]
    exact xm.right (k + 1)
  constructor
  · dsimp [Mills_seq]
    have : x.pnpow (3 ^ (k.val + 1)) = x.pnpow (3 ^ k.val) ^ 3 := by
      dsimp [pnpow]
      simp
      rw [pow_succ, rpow_mul]
      simp
    rw [this]
    apply fl_cub_le_cub_fl
  · exact lt_of_le_of_ne h₃ h₄
