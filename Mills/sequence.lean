import Mills.Defs

open Filter Topology NNReal

-- 不等式条件から収束についての結論を導くところを抽象化する
-- variableをやめて、定理としてかく

variable (seq : ℕ+ → ℕ+) (h : (n : ℕ+) → pnat_cube (seq n) ≤ seq (n + 1)) (h' : (n : ℕ+) → seq (n + 1) < pnat_cube ((seq n) + 1) - 1) (seq1gt1 : 1 < seq 1)

noncomputable def seq_left : (ℕ+ → ℝ≥0) := fun n ↦ cube_pow_rt (seq n) n

noncomputable def seq_right : (ℕ+ → ℝ≥0) := fun n ↦ cube_pow_rt (seq n + 1) n

lemma left_gt_1 : 1 < seq_left seq 1 := by
  rw [seq_left, cube_pow_rt, pnat_cube]; simp;
  apply one_lt_rpow _ (by simp)
  simp
  exact seq1gt1

lemma left_lt_right (n : ℕ+) : (seq_left seq) n < (seq_right seq) n := by
  rw [seq_left, seq_right]
  apply cpr_lt
  apply pnat_gt_succ

-- 順序同型を使って証明したい。monotoneの行き先の型を決めないでやりたい。αで。
lemma monotone_pnat_of_le_succ {f : ℕ+ → α} [Preorder α] (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  sorry

lemma strictAnti_pnat_of_succ_lt {f : ℕ+ → ℝ≥0} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  sorry
--  Nat.rel_of_forall_rel_succ_of_le (· ≤ ·) hf

lemma mono_seq : Monotone seq := by
  apply monotone_pnat_of_le_succ
  intro n
  calc
    seq n ≤ pnat_cube (seq n) := pnat_cube_le (seq n)
    _ ≤ seq (n + 1) := h n

lemma mono_left : Monotone (seq_left seq) := by
  apply monotone_pnat_of_le_succ
  intro n
  rw [seq_left, seq_left, pnpow_le_iff (pnat_cube (n + 1)), cpr_pnp (seq (n + 1)) (n + 1), cpr_pnp' (seq n) n]
  simp
  exact h n

lemma str_anti_right : StrictAnti (seq_right seq) := by
  apply strictAnti_pnat_of_succ_lt
  intro n
  rw [seq_right, seq_right, pnpow_lt_iff (pnat_cube (n + 1)), cpr_pnp (seq (n + 1) + 1) (n + 1), cpr_pnp' (seq n + 1) n, Nat.cast_lt, PNat.coe_lt_coe]
  calc
    seq (n + 1) + 1 < pnat_cube (seq n + 1) - 1 + 1 := by apply add_lt_add_right; apply h'
    _ = (pnat_cube (seq n + 1)).natPred.succPNat := by
      apply pred_succ
      calc
        1 < seq 1 := seq1gt1
        _ ≤ seq n := by apply mono_seq seq h (by simp)
        _ < seq n + 1 := by apply pnat_gt_succ
        _ ≤ pnat_cube (seq n + 1) := by apply pnat_cube_le
    _ = pnat_cube (seq n + 1) := by apply PNat.succPNat_natPred

lemma anti_right : Antitone (seq_right seq) := StrictAnti.antitone (str_anti_right seq h h' seq1gt1)

lemma bdd_left : BddAbove (Set.range (seq_left seq)) := by
  use (seq_right seq) 1
  intro x hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  calc
    (seq_left seq) n ≤ (seq_right seq) n := le_of_lt (left_lt_right seq n)
    _ ≤ (seq_right seq) 1 := anti_right seq h h' seq1gt1 (by norm_num)

lemma bdd_right : BddBelow (Set.range (seq_right seq)) := by
  use (seq_left seq) 1
  intro x hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  calc
    (seq_left seq) 1 ≤ (seq_left seq) n := mono_left seq h (by norm_num)
    _ ≤ (seq_right seq) n := le_of_lt (left_lt_right seq n)

noncomputable def left_lim : ℝ≥0 := sSup (Set.range (seq_left seq))

noncomputable def right_lim : ℝ≥0 := sInf (Set.range (seq_right seq))

lemma left_sup : IsLUB (Set.range (seq_left seq)) (left_lim seq) := by
  apply isLUB_csSup
  use (seq_left seq) 1
  use 1
  exact bdd_left seq h h' seq1gt1

lemma left_le_sup (n : ℕ+) : (seq_left seq) n ≤ left_lim seq := (left_sup seq h h' seq1gt1).left ⟨n, rfl⟩

lemma left_lim_nonneg : 0 ≤ left_lim seq := by simp

lemma left_lim_gt_1 : 1 < left_lim seq := by calc
  1 < (seq_left seq) 1 := left_gt_1 seq seq1gt1
  _ ≤ left_lim seq := left_le_sup seq h h' seq1gt1 1

lemma right_inf : IsGLB (Set.range (seq_right seq)) (right_lim seq) := by
  apply isGLB_csInf
  use (seq_right seq) 1
  use 1
  exact bdd_right seq h

lemma right_inf_lt (n : ℕ+) : right_lim seq < (seq_right seq) n := by
  by_contra hyp; push_neg at hyp
  have h₀ : seq_right seq (n + 1) < seq_right seq n := by apply str_anti_right seq h h' seq1gt1; rw [← PNat.coe_lt_coe]; simp
  have h₁ : seq_right seq (n + 1) < right_lim seq := by calc
    seq_right seq (n + 1) < seq_right seq n := h₀
    _ ≤ right_lim seq := hyp
  have h₂ : right_lim seq ≤ seq_right seq (n + 1) := by apply (right_inf seq h).left; use (n + 1)
  have : seq_right seq (n + 1) ≠ seq_right seq (n + 1) := ne_of_lt (lt_of_lt_of_le h₁ h₂)
  contradiction

lemma left_sup_le_right_inf : left_lim seq ≤ right_lim seq := by
  by_contra hyp; push_neg at hyp
  rcases IsLUB.exists_between (left_sup seq h h' seq1gt1) hyp with ⟨x, ⟨n, hx⟩, h₁⟩
  rcases IsGLB.exists_between (right_inf seq h) h₁.left with ⟨y, ⟨m, hy⟩, ⟨_, h₃⟩⟩
  let k := max n m
  have h₄ : seq_left seq n < seq_right seq m := by calc
    seq_left seq n ≤ seq_left seq k := mono_left seq h (le_max_left n m)
    _ < seq_right seq k := left_lt_right seq k
    _ ≤ seq_right seq m := anti_right seq h h' seq1gt1 (le_max_right n m)
  rw [← hx, ← hy] at h₃
  apply not_lt_of_lt h₄ h₃

lemma left_pow_eq_seq (n : ℕ+) : cube_pow_rt (seq n) n = seq_left seq n := rfl

lemma left_le_sup_pow (n : ℕ+) : (seq n) ≤ (left_lim seq).pnpow (pnat_cube n) := by
  rw [cube_le, left_pow_eq_seq seq n]
  apply left_le_sup seq h h' seq1gt1

lemma right_pow_eq_seq (n : ℕ+) : cube_pow_rt (seq n + 1) n = seq_right seq n := rfl

lemma right_inf_pow_lt (n : ℕ+) : (right_lim seq).pnpow (pnat_cube n) < (seq n + 1) := by
  have : @Nat.cast ℝ≥0 _ ((seq n + 1).val) = seq n + 1 := by simp
  rw [← this, cube_lt, right_pow_eq_seq seq n]
  apply right_inf_lt seq h h' seq1gt1

theorem left_floor_eq_seq (n : ℕ+) : Nat.floor ((left_lim seq).pnpow (pnat_cube n)) = seq n := by
    rw [Nat.floor_eq_iff]
    constructor
    · exact left_le_sup_pow seq h h' seq1gt1 n
    · calc
        (left_lim seq).pnpow (pnat_cube n) ≤ (right_lim seq).pnpow (pnat_cube n) := by
          apply pnpow_le (pnat_cube n) (left_sup_le_right_inf seq h h' seq1gt1)
        _ < (seq n + 1) := right_inf_pow_lt seq h h' seq1gt1 n
        _ = seq n + 1 := by simp
    simp

#check left_lim
#check left_floor_eq_seq
