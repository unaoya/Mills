import Mills.Defs

open NNReal

-- 補題6はミルズ定数でなく、一般のミルズ数についても成り立つ？
-- 最小性を使わない？（が実際の証明ではミルズ定数の場合しか使わない。）

-- 補題として1より大きい自然数nに対して(n+1)^3-1が合成数となることを示しておく。
lemma not_prime (n : ℕ+) (nge2 : 2 ≤ n) : ¬Nat.Prime (pnat_cube (n + 1) - 1) := by
  have h' : (n + 1) ^ 3 - 1 = n * (n ^ 2 + 3 * n + 3) := by sorry
--    ring_nf; rw [add_assoc, add_assoc, add_assoc, Nat.add_sub_self_left]
--  rw [h']
--  apply Nat.not_prime_mul (by linarith) (by simp)
  sorry

lemma lem6_left (k : ℕ+) (x : ℝ≥0) (_ : Mills x) : pnat_cube (Mills_seq x k) ≤ (Mills_seq x (k + 1)) := by
  have h₀ : Mills_seq x k ≤ x.pnpow (pnat_cube k) := by dsimp [Mills_seq]; apply Nat.floor_le (by simp)
  have h₁ : pnat_cube (Mills_seq x k) ≤ x.pnpow (pnat_cube (k + 1)) := by
    rw [pnat_cube_succ, pnpow, pnat_cube_val]
    simp
    rw [pow_mul]
    apply pow_le_pow_left (by simp) h₀
  have h₂ : Mills_seq x (k + 1) = Nat.floor (x.pnpow (pnat_cube (k + 1))) := by dsimp [Mills_seq, pnpow]
  rw [← Nat.le_floor_iff (by simp), ← h₂] at h₁
  exact h₁

lemma lem6_right (k : ℕ+) (x : ℝ≥0) (xm : Mills x) : (Mills_seq x (k + 1)) + 1 < pnat_cube (Mills_seq x k + 1) := by
  have h₀ : x.pnpow (pnat_cube k) < Mills_seq x k + 1 := by dsimp [Mills_seq]; apply Nat.lt_floor_add_one
  have h₁ : x.pnpow (pnat_cube (k + 1)) < pnat_cube (Mills_seq x k + 1) := by
    rw [pnat_cube_succ, pnpow, pnat_cube_val (Mills_seq x k + 1)]
    simp
    rw [pow_mul]
    apply pow_lt_pow_left h₀ (by simp) (by simp)
  have h₂ : Mills_seq x (k + 1) = Nat.floor (x.pnpow (pnat_cube (k + 1))) := by dsimp [Mills_seq, pnpow]
  have h₃ : Nat.floor (x.pnpow (pnat_cube (k + 1))) < pnat_cube (Mills_seq x k + 1) := by sorry
  have h₄ : Mills_seq x (k + 1) + 1 ≤ pnat_cube (Mills_seq x k + 1) := by sorry
  have h₅ : Mills_seq x (k + 1) + 1 ≠ pnat_cube (Mills_seq x k + 1) := by
    intro h
    have : (Mills_seq x (k + 1) + 1).val = (pnat_cube (Mills_seq x k + 1)).val := by rw [h]
    simp at this
    have : ↑(Mills_seq x (k + 1)) = ↑(pnat_cube (Mills_seq x k + 1)) - 1 := Nat.eq_sub_of_add_eq this
    apply not_prime (Mills_seq x k) (Mills_seq_ge_2 x k xm)
    rw [← this]
    exact xm.right (k + 1)
  exact lt_of_le_of_ne h₄ h₅

-- 引き算したくないので移項する
lemma lem6 (k : ℕ+) (x : ℝ≥0) (xm : Mills x) : pnat_cube (Mills_seq x k) ≤ (Mills_seq x (k + 1)) ∧ (Mills_seq x (k + 1)) + 1 < pnat_cube (Mills_seq x k + 1) :=
  ⟨lem6_left k x xm, lem6_right k x xm⟩
