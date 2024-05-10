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

-- floorや冪乗周りを先に揃えておく
-- 冪乗の指数は非負実数か正の整数？
-- 3の冪乗がいっぱい出てくる

-- 一般的な設定でできる不等式は先に証明しておく

-- 3 ^ n のところも型をきちんと決めておいたほうがいいかも
-- 3 ^ n なのか 3 ^ n.valなのか
lemma Mills_seq_ge_2 (x : ℝ≥0) (n : ℕ+) (h : Mills x) : 2 ≤ Mills_seq x n := (Nat.prime_def_lt.1 (h.right n)).1

lemma hfloor (n : ℕ) (x : ℝ) (h : n ≤ Nat.floor x) (xpos : 0 ≤ x) : n ≤ x := by calc
  (n : ℝ) ≤ Nat.floor x := by sorry --apply (nat_real_le n _).2 h
  _ ≤ x := by apply Nat.floor_le xpos

def Mills_lb (x : ℝ≥0) (h : Mills x) : 2 ≤ x.pnpow 3 := by
  have h₁ : 2 ≤ Mills_seq x 1 := Mills_seq_ge_2 x 1 h
  dsimp [Mills_seq] at h₁
  have h₂ : Nat.floor (x.pnpow 3) ≤ x.pnpow 3 := by apply Nat.floor_le; simp
  simp at h₁
  sorry


lemma Mills_not_nat (A : ℝ≥0) (h : Mills A) : ∀ n : ℕ, A ≠ n := by
  intro n hn
  have : Mills_seq A 1 = n ^ 3 :=  by
    simp [Mills_seq, hn, pnpow]
    sorry
--    rw [← Real.rpow_natCast, ← cast_nat_pow_eq_rpow_cast, Nat.floor_coe]; simp
  have : ¬Nat.Prime (Mills_seq A 1) := by rw [this]; exact Nat.Prime.not_prime_pow (by simp)
  have : Nat.Prime (Mills_seq A 1) := h.right 1
  contradiction

-- ライブラリにない？非負整数は自然数である。
lemma nonneg_int_is_nat (n : ℤ) (h : 0 ≤ n) : ∃ m : ℕ, n = m := by -- 型の合わせ方は明示する？
  sorry

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

noncomputable def min_dist (x : ℝ) : ℝ := |x - round x|

lemma min_dist_fract (x : ℝ) : min_dist x = min (Int.fract x) (1 - Int.fract x) := abs_sub_round_eq_min x

lemma floor_cast (x : ℝ) (xpos : 0 ≤ x) : (Nat.cast : ℕ → ℝ) (Nat.floor x) = (Int.cast : ℤ → ℝ) (Int.floor x) := by
  apply natCast_floor_eq_intCast_floor
  exact xpos

-- Nat.floorにする必要ある？Int.floorでもいい？
lemma min_dist_floor (x : ℝ) (xpos : 0 ≤ x) : min_dist x ≤ |x - Nat.floor x| := by
  rw [natCast_floor_eq_intCast_floor xpos, min_dist_fract, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg x)]
  exact min_le_left _ _

-- notation: "∥" x "∥" => min_dist A
-- n₀は実数が本来かもしれないが、こっちも出るはず
axiom Mahler (r : ℚ) (ε : ℝ) (h₁ : 1 < r) (h₂ : ∀ n : ℕ, ↑n ≠ r) :
∃ n₀ : ℕ, n₀ > 0 ∧ ∀ n ≥ n₀, min_dist (r ^ (n : ℝ)) > Real.exp (-ε * (n : ℝ))

theorem Mills_irrational : Irrational A := by
  intro h
  rcases h with ⟨r, hr⟩
  have h₁ : 1 < r := by
    have : Rat.cast 1  < (r : ℝ) := by rw [hr]; simp; sorry
    apply Rat.cast_lt.1 this
  -- rをℚ≥0にしたほうがいいかも？
  rcases lem7 with ⟨γ, _, k₁, _, h₃⟩
  rcases Mahler r γ h₁ h₂ with ⟨K, h₄⟩
  let k := max K k₁
  have h₅ : K ≤ 3 ^ k := by
    calc
      K ≤ k := le_max_left K k₁
      _ ≤ 3 ^ k := by apply le_of_lt (Nat.lt_pow_self (by norm_num) k)
  have h₆ : min_dist (r ^ 3 ^ k) > Real.exp (-γ * 3 ^ k) := by
    have : Nat.pow 3 k = (3 : ℝ) ^ k := by simp -- 抽象化
    calc
      min_dist (r.pow 3 ^ k) = min_dist (r.rpow (3 ^ k : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_natCast]; simp
      _ > Real.exp (-γ * 3 ^ k) := by rw [← this]; apply h₄.right (3 ^ k) h₅
  have h₇ : min_dist (r.rpow 3 ^ k) ≤ Real.exp (-γ * 3 ^ k) := by
    calc
      min_dist (r ^ 3 ^ k) ≤ |(r : ℝ) ^ 3 ^ k - Nat.floor ((r : ℝ) ^ 3 ^ k)| := by
        apply min_dist_floor
        rw [h, ← Real.rpow_natCast]
        apply Real.rpow_nonneg (by linarith [Mills_gt_one])
      _ = |A ^ 3 ^ k - Nat.floor (A ^ 3 ^ k)| := by rw [h]
      _ = |A ^ (3 : ℝ) ^ k - Nat.floor (A ^ (3 : ℝ) ^ k)| := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        have : (Nat.cast : ℕ → ℝ) (Nat.pow 3 k) = (3 : ℝ) ^ (k : ℝ) := by simp --抽象化
        rw [← this]; simp
      _ = |A ^ (3 : ℝ) ^ k - p' k| := by rw [p'eqp''', p''', ← Real.rpow_natCast]
      _ ≤ Real.exp (-γ * 3 ^ k) := h₃ k (le_max_right K k₁)
  linarith
