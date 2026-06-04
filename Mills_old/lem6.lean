import Mills.Defs

open NNReal

-- 補題6はミルズ定数でなく、一般のミルズ数についても成り立つ？
-- 最小性を使わない？（が実際の証明ではミルズ定数の場合しか使わない。）

-- 補題として1より大きい自然数nに対して(n+1)^3-1が合成数となることを示しておく。
lemma not_prime' (n : ℕ) (hn : 2 ≤ n) : ¬Nat.Prime ((n + 1) ^ 3 - 1) := by
  have : (n + 1) ^ 3 - 1 = n * (n ^ 2 + 3 * n + 3) := by
    ring_nf
    rw [add_assoc, add_assoc, Nat.add_sub_self_left]
    ring_nf
  rw [this]
  apply Nat.not_prime_mul (by linarith) (by simp)

lemma not_prime (n : ℕ+) (nge2 : 2 ≤ n) : ¬Nat.Prime (pnat_cube (n + 1) - 1) := by
  have : (pnat_cube (n + 1)).val - 1 = (n.val + 1) ^ 3 - 1 := by
    rw [pnat_cube_val]
    simp
  rw [this]
  apply not_prime' n.val nge2

lemma pnpow_mul (x : ℝ≥0) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  sorry

lemma lem6_left (k : ℕ+) (x : ℝ≥0) (_ : Mills x) :
    pnat_cube (Mills_seq x k) ≤ (Mills_seq x (k + 1)) := by
  have h₁ : pnat_cube (Mills_seq x k) ≤ x ^ (pnat_cube (k + 1)) := by
    rw [pnat_cube_succ, pnat_cube_val]
    simp
    rw [pnpow_mul]
    apply pow_le_pow_left₀
    simp
    apply Nat.floor_le
    simp
  rw [← Nat.le_floor_iff (by simp)] at h₁
  exact h₁

lemma lem6_right (k : ℕ+) (x : ℝ≥0) (hx : x > 1) (xm : Mills x) :
    (Mills_seq x (k + 1)) + 1 < pnat_cube (Mills_seq x k + 1) := by
  have h₁ : x ^ (pnat_cube (k + 1)) < pnat_cube (Mills_seq x k + 1) := by
    rw [pnat_cube_succ, pnat_cube_val (Mills_seq x k + 1)]
    simp
    rw [pnpow_mul]
    apply pow_lt_pow_left₀
    apply Nat.lt_floor_add_one
    simp
    simp
  -- have h₃ : Nat.floor (x ^ (pnat_cube (k + 1))) < pnat_cube (Mills_seq x k + 1) := by
  --   calc
  --     Nat.floor (x ^ (pnat_cube (k + 1))) ≤ x ^ (pnat_cube (k + 1)) := by
  --       sorry
  --     _ < pnat_cube (Mills_seq x k + 1) := h₁
  have h₄ : Mills_seq x (k + 1) + 1 ≤ pnat_cube (Mills_seq x k + 1) := by
    sorry
    -- calc
    --   Mills_seq x (k + 1) + 1 = Nat.floor (x ^ (pnat_cube (k + 1))) + 1 := by
    --     dsimp [Mills_seq]
    --   _ ≤ x ^ (pnat_cube (k + 1)) + 1 := by
    --     apply Nat.le_succ_of_floor
    --   _ < pnat_cube (Mills_seq x k + 1) + 1 := by
    --     exact h₁
  have h₅ : Mills_seq x (k + 1) + 1 ≠ pnat_cube (Mills_seq x k + 1) := by
    intro h
    have : (Mills_seq x (k + 1) + 1).val = (pnat_cube (Mills_seq x k + 1)).val := by rw [h]
    simp at this
    have : (Mills_seq x (k + 1)).val = (pnat_cube (Mills_seq x k + 1)) - 1 := Nat.eq_sub_of_add_eq this
    apply not_prime (Mills_seq x k) (Mills_seq_ge_2 x hx k xm)
    rw [← this]
    exact xm.right (k + 1)
  exact lt_of_le_of_ne h₄ h₅

-- 引き算したくないので移項する
lemma lem6 (k : ℕ+) (x : ℝ≥0) (hx : x > 1)  (xm : Mills x) :
    pnat_cube (Mills_seq x k) ≤ (Mills_seq x (k + 1)) ∧ (Mills_seq x (k + 1)) + 1 < pnat_cube (Mills_seq x k + 1) :=
  ⟨lem6_left k x xm, lem6_right k x hx xm⟩
