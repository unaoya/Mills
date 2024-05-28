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
import Mills.lem7

open Filter Topology NNReal

-- floorや冪乗周りを先に揃えておく
-- 冪乗の指数は非負実数か正の整数？
-- 3の冪乗がいっぱい出てくる

-- 一般的な設定でできる不等式は先に証明しておく

lemma hfloor (n : ℕ) (x : ℝ) (h : n ≤ Nat.floor x) (xpos : 0 ≤ x) : n ≤ x := by calc
  (n : ℝ) ≤ Nat.floor x := by sorry --apply (nat_real_le n _).2 h
  _ ≤ x := by apply Nat.floor_le xpos

lemma Mills_not_nat (A : ℝ≥0) (h : Mills A) : ∀ n : ℕ, A ≠ n := by
  intro n hn
  have : Mills_seq A 1 = n ^ 3 :=  by
    simp [Mills_seq, hn, pnpow]
    have : ((Nat.cast : ℕ → ℝ≥0) n) ^ 3 = Nat.cast (n ^ 3) := by simp
    rw [this, Nat.floor_coe]
  have : ¬Nat.Prime (Mills_seq A 1) := by rw [this]; exact Nat.Prime.not_prime_pow (by simp)
  have : Nat.Prime (Mills_seq A 1) := h.right 1
  contradiction

-- ライブラリにない？非負整数は自然数である。
lemma nonneg_int_is_nat (n : ℤ) (h : 0 ≤ n) : ∃ m : ℕ, n = m := by -- 型の合わせ方は明示する？
  sorry

/-
lemma nat_pos (r : ℝ≥0) (h : 1 < r) (n : ℤ) (hn : n = r) : n ∈ Set.range Nat.cast := by
  rw [← hn] at h
  apply Int.cast_lt.mp at h
  have h' : 0 ≤ n := by
    calc
      0 ≤ Int.ofNat 1 := by norm_num
      _ ≤ n := le_of_lt h
  rcases Int.eq_ofNat_of_zero_le h' with ⟨m, hm⟩
  exact ⟨m, hm.symm⟩

-- 型を合わせるだけで、数学的な内容はほぼない。
lemma Mills_not_int (A : ℝ≥0) (h : Mills A) : ∀ n : ℤ, A.toReal ≠ n := by
  intro n hn
  have h₁ : 1 < n := by sorry
  rcases (nat_pos A h.left n hn) with ⟨m, hm⟩
  have ⟨h₁, _⟩ := h
  rw [← NNReal.one_lt_coe] at h₁
  rw [hn, ← hm] at h₁
  apply Mills_not_nat A h m
  rw [← hm] at hn
  sorry

lemma min_dist_fract (x : ℝ) : min_dist x = min (Int.fract x) (1 - Int.fract x) := abs_sub_round_eq_min x

lemma floor_cast (x : ℝ) (xpos : 0 ≤ x) : (Nat.cast : ℕ → ℝ) (Nat.floor x) = (Int.cast : ℤ → ℝ) (Int.floor x) := by
  apply natCast_floor_eq_intCast_floor
  exact xpos

-- notation: "∥" x "∥" => min_dist A
-- n₀は実数が本来かもしれないが、こっちも出るはず
-/

noncomputable def min_dist (x : ℝ) : ℝ := |x - round x|

lemma min_dist_fract (x : ℝ) : min_dist x = min (Int.fract x) (1 - Int.fract x) := abs_sub_round_eq_min x

-- Nat.floorにする必要ある？Int.floorでもいい？
lemma min_dist_floor (x : ℝ) (xpos : 0 ≤ x) : min_dist x ≤ |x - Nat.floor x| := by
  rw [natCast_floor_eq_intCast_floor xpos, min_dist_fract, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg x)]
  exact min_le_left _ _

axiom Mahler (r : ℚ) (ε : ℝ) (h₁ : 1 < r) (h₂ : ∀ n : ℕ, ↑n ≠ r) :
∃ n₀ : ℕ+, ∀ n ≥ n₀, min_dist (r ^ n.val) > Real.exp (-ε * (n : ℝ))

theorem Mills_irrational2 : Irrational A := by
  rintro ⟨r, hr⟩
  have h₁ : 1 < r := by
    apply (@Rat.cast_lt ℝ).1
    rw [hr]; simp; sorry
  have h₂ : ∀ n : ℕ, ↑n ≠ r := by sorry
  rcases lem7 with ⟨γ, γpos, k₁, hγ⟩
  rcases Mahler r γ h₁ h₂ with ⟨K, h₄⟩
  let k := max K k₁
  have h₅ : K ≤ (pnat_cube k) := by
    calc
      K ≤ k := le_max_left K k₁
      _ ≤ (pnat_cube k) := by apply le_of_lt (Nat.lt_pow_self _ k.val); simp
  have h₆ : min_dist (r ^ (pnat_cube k).val) > Real.exp (-γ * ((pnat_cube k))) := by apply h₄ (pnat_cube k) h₅
  have h₇ : min_dist (r ^ (pnat_cube k).val) ≤ Real.exp (-γ * (pnat_cube k)) := by
    calc
      min_dist (r ^ (pnat_cube k).val) = min_dist (A.val ^ (pnat_cube k).val) := by rw [hr]; simp
      _ ≤ |A.val ^ (pnat_cube k).val - Nat.floor (A.val ^ (pnat_cube k).val)| := by apply min_dist_floor; simp
      _ ≤ |A.val ^ (pnat_cube k).val - Nat.floor (A ^ (pnat_cube k).val)| := by sorry
      _ = |↑(A.rpow (pnat_cube k)) - ↑(Mills_seq A k)| := by dsimp [rpow, Mills_seq, pnpow]; simp
      _ ≤ Real.exp (-γ * (pnat_cube k)) := hγ k (le_max_right K k₁)
  linarith
