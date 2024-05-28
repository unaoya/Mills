import Mills.Defs

open Filter Topology NNReal

-- 不等式条件から収束についての結論を導くところを抽象化する
-- variableをやめて、定理としてかく
section

variable (seq : ℕ+ → ℕ+) (h : (n : ℕ+) → pnat_cube (seq n) ≤ seq (n + 1)) (h' : (n : ℕ+) → seq (n + 1) < pnat_cube ((seq n) + 1) - 1) (seq1gt1 : 1 < seq 1)

noncomputable def cube_pow_rt (n k : ℕ+) : ℝ≥0 := (n : ℝ≥0).rpow (1 / (pnat_cube k) : ℝ≥0)

noncomputable def seq_left : (ℕ+ → ℕ+) → (ℕ+ → ℝ≥0) := fun seq n ↦ cube_pow_rt (seq n) n

noncomputable def seq_right : (ℕ+ → ℕ+) → (ℕ+ → ℝ≥0) := fun seq n ↦ cube_pow_rt (seq n + 1) n

lemma rseqnonneg (n : ℕ+) : 0 ≤ (Nat.cast : ℕ → ℝ) (seq n) := by simp

lemma left_nonneg (n : ℕ+) : 0 ≤ seq_left seq n := by simp

lemma left_gt_1 : 1 < seq_left seq 1 := by
  rw [seq_left, cube_pow_rt, pnat_cube]; simp;
  apply one_lt_rpow _ (by simp)
  simp
  exact seq1gt1

lemma left_lt_right (n : ℕ+) : (seq_left seq) n < (seq_right seq) n := by
  rw [seq_left, seq_right, cube_pow_rt, cube_pow_rt, pnat_cube]
  simp
  apply Real.rpow_lt_rpow (by apply rseqnonneg) (by norm_num) (by simp)

lemma mono_left : Monotone (seq_left seq) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [seq_left, seq_left]
  have : 0 < (Nat.cast : ℕ → ℝ) 3 ^ (n + 1) := by norm_num
  rw [← Real.rpow_le_rpow_iff (by apply Real.rpow_nonneg (by apply rseqnonneg)) (by apply Real.rpow_nonneg (by apply rseqnonneg)) this]
  rw [← Real.rpow_mul (by apply rseqnonneg), ← Real.rpow_mul (by apply rseqnonneg), div_mul, div_mul, ← div_mul]
  ring_nf
  field_simp
  have : ((Nat.cast : ℕ → ℝ) (seq n)) ^ (OfNat.ofNat 3 : ℝ) = (Nat.cast : ℕ → ℝ) ((seq n) ^ 3) := by
    simp
    rw [← Real.rpow_natCast]
    apply congrArg
    simp
  rw [this, Nat.cast_le, add_comm]
  exact (h n)

lemma str_anti_right : StrictAnti (seq_right seq) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have : 0 < (3 : ℝ) ^ (n + 1) := by norm_num
  rw [← Real.rpow_lt_rpow_iff (by apply Real.rpow_nonneg (by linarith [rpnonneg])) (by apply Real.rpow_nonneg (by linarith [rpnonneg])) this]
  rw [seq_right, seq_right]
  rw [← Real.rpow_mul (by linarith [rpnonneg]), ← Real.rpow_mul (by linarith [rpnonneg])]
  ring_nf
  field_simp
  have : (1 + (Nat.cast : ℕ → ℝ) (seq n)) ^ (OfNat.ofNat 3 : ℝ) = (Nat.cast : ℕ → ℝ) ((1 + (seq n)) ^ 3) := by
    simp
    rw [← Real.rpow_natCast]
    apply congrArg
    simp
  rw [this, add_comm, ← lt_add_neg_iff_add_lt, ← sub_eq_add_neg]
  have : OfNat.ofNat 1 = (Nat.cast : ℕ → ℝ) 1 := by simp
  rw [this, ← Nat.cast_sub, Nat.cast_lt, add_comm, add_comm 1 (seq n)]
  exact (h' n)
  rw [← one_pow 3]
  apply pow_le_pow_left
  linarith
  simp

lemma anti_right : Antitone (seq_right seq) := StrictAnti.antitone (str_anti_right seq)

lemma bdd_left : BddAbove (Set.range (seq_left seq)) := by
  use (seq_right seq) 1
  intro x hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  calc
    (seq_left seq) n ≤ (seq_right seq) n := le_of_lt (left_lt_right seq n)
    _ ≤ (seq_right seq) 1 := anti_right seq (by norm_num)

lemma bdd_right : BddBelow (Set.range (seq_right seq)) := by
  use (seq_left seq) 1
  intro x hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  calc
    (seq_left seq) 1 ≤ (seq_left seq) n := mono_left seq (by norm_num)
    _ ≤ (seq_right seq) n := le_of_lt (left_lt_right seq n)

noncomputable def left_lim : ℝ≥0 := sSup (Set.range (seq_left seq))

noncomputable def right_lim : ℝ≥0 := sInf (Set.range (seq_right seq))

lemma left_sup : IsLUB (Set.range (seq_left seq)) (left_lim seq) := by
  apply isLUB_csSup
  use (seq_left seq) 1
  use 1
  exact bdd_left seq

lemma left_le_sup (n : ℕ+) : (seq_left seq) n ≤ left_lim seq := (left_sup seq).left ⟨n, rfl⟩

lemma left_lim_nonneg : 0 ≤ left_lim seq := by simp

lemma left_lim_gt_1 : 1 < left_lim seq := by calc
  1 < (seq_left seq) 1 := left_gt_1 seq seq1gt1
  _ ≤ left_lim seq := left_le_sup seq 1

lemma right_inf : IsGLB (Set.range (seq_right seq)) (right_lim seq) := by
  apply isGLB_csInf
  use (seq_right seq) 1
  use 1
  exact bdd_right seq

lemma right_inf_lt (n : ℕ+) : right_lim seq < (seq_right seq) n := by
  by_contra hyp; push_neg at hyp
  have : seq_right seq (n + 1) < seq_right seq n := by apply str_anti_right seq; sorry
  have : seq_right seq (n + 1) < right_lim seq := by sorry
  have : right_lim seq ≤ seq_right seq (n + 1) := by apply (right_inf seq).left; use (n + 1)
  sorry

lemma left_sup_le_right_inf : left_lim seq ≤ right_lim seq := by
  by_contra hyp; push_neg at hyp
  rcases IsLUB.exists_between (left_sup seq) hyp with ⟨x, ⟨n, _⟩, h₁⟩
  rcases IsGLB.exists_between (right_inf seq) h₁.left with ⟨y, ⟨m, _⟩, h₃⟩
  let k := max n m
  have : (seq_right seq) k ≤ (seq_right seq) m := anti_right seq (le_max_right n m)
  have : (seq_left seq) n ≤ (seq_left seq) k := mono_left seq (le_max_left n m)
  have : (seq_left seq) k < (seq_right seq) k := left_lt_right seq k
  sorry

lemma left_pow_eq_seq (n : ℕ+) : cube_pow_rt (seq n) n = seq_left seq n := rfl

lemma cube_le (n m : ℕ+) (x : ℝ≥0) : n ≤ x.pnpow (pnat_cube m) ↔ cube_pow_rt n m ≤ x := sorry

lemma left_le_sup_pow (n : ℕ+) : (seq n) ≤ (left_lim seq).pnpow (pnat_cube n) := by
  rw [cube_le, left_pow_eq_seq seq n]
  apply left_le_sup

lemma right_pow_eq_seq (n : ℕ+) : cube_pow_rt (seq n + 1) n = seq_right seq n := rfl

lemma cube_lt (n m : ℕ+) (x : ℝ≥0) : x.pnpow (pnat_cube m) < n ↔ x < cube_pow_rt n m := sorry

lemma right_inf_pow_lt (n : ℕ+) : (right_lim seq).pnpow (pnat_cube n) < (seq n + 1) := by
  have : @Nat.cast ℝ≥0 _ ((seq n + 1).val) = seq n + 1 := by simp
  rw [← this, cube_lt, right_pow_eq_seq seq n]
  apply right_inf_lt seq

lemma pnpow_le {x y : ℝ≥0} (n : ℕ+) (h: x ≤ y) : x.pnpow n ≤ y.pnpow n := by sorry

lemma left_floor_eq_seq (n : ℕ+) : Nat.floor ((left_lim seq).pnpow (pnat_cube n)) = seq n := by
    rw [Nat.floor_eq_iff]
    constructor
    · exact left_le_sup_pow seq n
    · calc
        (left_lim seq).pnpow (pnat_cube n) ≤ (right_lim seq).pnpow (pnat_cube n) := by
          apply pnpow_le (pnat_cube n) (left_sup_le_right_inf seq)
        _ < (seq n + 1) := right_inf_pow_lt seq n
        _ = seq n + 1 := by simp
    simp
