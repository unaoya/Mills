import Mills.Defs
import Mills.prop4
import Mills.lem7

open Filter Topology NNReal

-- floorや冪乗周りを先に揃えておく
-- 冪乗の指数は非負実数か正の整数？
-- 3の冪乗がいっぱい出てくる

-- 一般的な設定でできる不等式は先に証明しておく

lemma Mills_not_nat (A : ℝ≥0) (h : Mills A) : ∀ n : ℕ+, A ≠ n := by
  intro n hn
  have : Mills_seq A 1 = n ^ 3 :=  by
    rw [Mills_seq, pnpow, pnat_cube, hn]
    simp
    have : ((Nat.cast : ℕ → ℝ≥0) n) ^ 3 = Nat.cast (n ^ 3) := by simp
    rw [this, Nat.floor_coe]
  have : ¬Nat.Prime (Mills_seq A 1) := by rw [this]; exact Nat.Prime.not_prime_pow (by norm_num)
  have : Nat.Prime (Mills_seq A 1) := h.right 1
  contradiction

noncomputable def min_dist (x : ℝ) : ℝ := |x - round x|

lemma min_dist_fract (x : ℝ) : min_dist x = min (Int.fract x) (1 - Int.fract x) := abs_sub_round_eq_min x

lemma min_dist_floor (x : ℝ) (xpos : 0 ≤ x) : min_dist x ≤ |x - Nat.floor x| := by
  rw [natCast_floor_eq_intCast_floor xpos, min_dist_fract, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg x)]
  exact min_le_left _ _

axiom Mahler (r : ℚ) (ε : ℝ) (h₁ : 1 < r) (h₂ : ∀ n : ℕ+, ↑n ≠ r) :
∃ n₀ : ℕ+, ∀ n ≥ n₀, min_dist (r ^ n.val) > Real.exp (-ε * (n : ℝ))

theorem Mills_irrational2 : Irrational A := by
  rintro ⟨r, hr⟩
  have h₁ : 1 < r := by
    apply (@Rat.cast_lt ℝ).1
    rw [hr]; simp; exact Mills_gt_one
  have h₂ : ∀ n : ℕ+, ↑n ≠ r := by
    intro n hn
    apply Mills_not_nat A Mills_exists n
    apply NNReal.eq
    rw [← hr, ← hn]
    simp
  rcases lem7 with ⟨γ, _, k₁, hγ⟩
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
      _ = |A.val ^ (pnat_cube k).val - Nat.floor (A ^ (pnat_cube k).val)| := by
        apply congr_arg; simp; apply congr_arg; simp
      _ = |↑(A.pnpow (pnat_cube k)) - ↑(Mills_seq A k)| := by dsimp [Mills_seq, pnpow]
      _ ≤ Real.exp (-γ * (pnat_cube k)) := hγ k (le_max_right K k₁)
  linarith
