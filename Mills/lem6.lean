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

lemma lem6 (k : ℕ+) (x : ℝ≥0) (xm : Mills x) : (Mills_seq x k) ^ 3 ≤ (Mills_seq x (k + 1)) ∧ (Mills_seq x (k + 1)) < (Mills_seq x k + 1) ^ 3 - 1 := by
  have h₀₀ : Mills_seq x k ≤ x.pnpow (pnat_cube k) := Nat.floor_le (by simp)
  have h₀₁ : x.pnpow (pnat_cube k) < Mills_seq x k + 1 := Nat.lt_floor_add_one _
  have h₁₀ : (Mills_seq x k) ^ 3 ≤ x.pnpow (pnat_cube (k + 1)) := by
    dsimp [Mills_seq, pnpow] at *
    rw [pnat_cube_succ]
    simp
    rw [pow_mul]
    apply pow_le_pow_left (by simp) h₀₀
  have h₁₁ : x.pnpow (pnat_cube (k + 1)) < (Mills_seq x k + 1) ^ 3 := by
    dsimp [Mills_seq, pnpow] at *
    rw [pnat_cube_succ]
    simp
    rw [pow_mul]
    apply pow_lt_pow_left h₀₁ (by simp) (by linarith)
  have h₂ : Mills_seq x (k + 1) = Nat.floor (x.pnpow (pnat_cube (k + 1))) := by dsimp [Mills_seq, pnpow]
  have h₃ : Mills_seq x (k + 1) ≤ (Mills_seq x k + 1) ^ 3 - 1:= by
    have : Mills_seq x (k + 1) < (Mills_seq x k + 1) ^ 3 := by
      rw [h₂, ← @Nat.cast_lt ℝ≥0]; simp
      calc
        ↑⌊x.pnpow (pnat_cube (k + 1))⌋₊ ≤ x.pnpow (pnat_cube (k + 1)) := by apply Nat.floor_le (by simp)
        _ < (Mills_seq x k + 1) ^ 3 := by apply h₁₁
    rw [← Nat.lt_iff_le_pred (by simp)]
    exact this
  have h₄ : Mills_seq x (k + 1) ≠ (Mills_seq x k + 1) ^ 3 - 1 := by
    intro h
    apply not_prime (Mills_seq x k) (Mills_seq_ge_2 x k xm)
    rw [← h]
    exact xm.right (k + 1)
  constructor
  · rw [h₂]
    apply (Nat.le_floor_iff (by simp)).2
    simp
    exact h₁₀
  · exact lt_of_le_of_ne h₃ h₄
