import Mills.Lemmas
import Mills.Defs

open Filter Topology NNReal

def Step' : ℕ → ℕ → Prop := fun p q => p ^ 3 ≤ q ∧ (Nat.cast : ℕ → ℝ) q ≤ (Nat.cast : ℕ → ℝ) p ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) p ^ (((Nat.cast : ℕ → ℝ) 3) * θ) ∧ q < (p + 1) ^ 3 - 1 ∧ Nat.Prime q

lemma Step_aux (n m : ℕ) (h : n ^ 3 ≤ m) (h' : BHP_const_nat ≤ n) : BHP_const_nat ≤ m := by
  have : 3 ≠ 0 := by linarith [BHP_const_nat_ge2]
  linarith [Nat.le_self_pow this n]

--これは一般的な補題なので外に切り出す、後でも再証明してる？
lemma aux : ∀ x : ℝ, BHP_const ≤ x → x ^ (Nat.cast : (ℕ → ℝ)) 3 + x ^ ((Nat.cast : ℕ → ℝ) 3 * θ) < (x + 1) ^ (Nat.cast : ℕ → ℝ) 3 - 1 := by
  intro x hx
  have : (Nat.cast : (ℕ → ℝ)) 3 * θ < (Nat.cast : (ℕ → ℝ)) 2 := by rw [θ]; norm_num;
  calc
    x ^ (Nat.cast : (ℕ → ℝ)) 3 + x ^ ((Nat.cast : (ℕ → ℝ)) 3 * θ) < x ^ (Nat.cast : (ℕ → ℝ)) 3 + x ^ (Nat.cast : (ℕ → ℝ)) 2 := add_lt_add_left (Real.rpow_lt_rpow_of_exponent_lt (by linarith [BHP_const_ge2]) this) (x ^ (Nat.cast : (ℕ → ℝ)) 3)
    _ ≤ x ^ (Nat.cast : (ℕ → ℝ)) 3 + 3 * x ^ (Nat.cast : (ℕ → ℝ)) 2 := by
      have : 0 ≤ x ^ (Nat.cast : (ℕ → ℝ)) 2 := Real.rpow_nonneg (by linarith [BHP_const_ge2]) ((Nat.cast : ℕ → ℝ) 2)
      linarith
    _ ≤ x ^ (Nat.cast : (ℕ → ℝ)) 3 + 3 * x ^ (Nat.cast : (ℕ → ℝ)) 2 + 3 * x := by linarith [BHP_const_ge2]
    _ = (x + 1) ^ (Nat.cast : (ℕ → ℝ)) 3 - 1 := by rw [Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]; ring_nf

lemma Stepex : ∀ p : ℕ, BHP_const_nat ≤ p → ∃ (q : ℕ), Step' p q := by
  intro p hp
  have hp' : BHP_const ≤ p := by calc
    BHP_const ≤ BHP_const_nat := by apply Nat.le_ceil
    _ ≤ p := by rw [Nat.cast_le]; exact hp
  have : BHP_const_nat ≤ p ^ 3 := by calc
    BHP_const_nat ≤ p := hp
    _ ≤ p ^ 3 := by apply Nat.le_self_pow (by linarith)
  rcases BHP_const_nat_BHP (p ^ 3) this with ⟨q, hq₁, hq₂, hq₃⟩
  use q
  have hq₅ : (Nat.cast : ℕ → ℝ) q ≤ (Nat.cast : ℕ → ℝ) p ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) p ^ (((Nat.cast : ℕ → ℝ) 3) * θ) := by
    have : (Nat.cast : ℕ → ℝ) (p ^ 3) = (Nat.cast : ℕ → ℝ) p ^ (Nat.cast : ℕ → ℝ) 3 := by simp [← Real.rpow_natCast]
    rw [this, ← Real.rpow_mul (by linarith [BHP_const_ge2])] at hq₂
    exact hq₂
  have hq₄ : q < (p + 1) ^ 3 - 1 := by
    have : (Nat.cast : (ℕ → ℝ)) q < (Nat.cast : (ℕ → ℝ)) ((p + 1) ^ 3 - 1) := by calc
      (Nat.cast : (ℕ → ℝ)) q ≤ (Nat.cast : ℕ → ℝ) p ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) p ^ (((Nat.cast : ℕ → ℝ) 3) * θ) := hq₅
      _ <  (((Nat.cast : (ℕ → ℝ)) p + 1) ^ (Nat.cast : (ℕ → ℝ)) 3 - 1) := aux p hp'
      _ = (Nat.cast : (ℕ → ℝ)) ((p + 1) ^ 3 - 1) := by simp; rw [← Real.rpow_natCast]; ring_nf
    exact Nat.cast_lt.1 this
  exact ⟨hq₁, hq₅, hq₄, hq₃⟩

noncomputable instance (m : ℕ) : DecidablePred (Step' m) :=
  by exact Classical.decRel Step' m

def NgeBHP : Type := {n : ℕ // BHP_const_nat ≤ n}

-- defじゃなくてletとかで証明の内部でやりたいけど、できる？
-- これはAを使って作ったやつじゃなくて、適当な初期値から作ったやつ。
noncomputable def pp' : ℕ → NgeBHP
| 0 => ⟨BHP_const_nat, le_refl BHP_const_nat⟩
| (n + 1) => ⟨Nat.find (Stepex (pp' n).val (pp' n).property), Step_aux (pp' n).val (Nat.find (Stepex (pp' n).val (pp' n).property)) (Nat.find_spec (Stepex (pp' n).val (pp' n).property)).left (pp' n).property⟩

noncomputable def pp : ℕ → ℕ := fun n ↦ (pp' n).val

lemma hpp' : ∀ k : ℕ, Step' (pp k) (pp (k + 1)) := by intro k; exact Nat.find_spec (Stepex (pp' k).val (pp' k).property)

lemma hpp : ∀ k : ℕ, (pp k) ^ 3 ≤ pp (k + 1) ∧ (Nat.cast : ℕ → ℝ) (pp (k + 1)) ≤ (Nat.cast : ℕ → ℝ) (pp k) ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) (pp k) ^ (((Nat.cast : ℕ → ℝ) 3) * θ) ∧ pp (k + 1) < ((pp k) + 1) ^ 3 - 1 ∧ Nat.Prime (pp (k + 1)) := fun k ↦ hpp' k

lemma pnonneg (n : ℕ) : 0 ≤ pp n := by linarith [(Nat.prime_def_lt.1 (hpp n).2.2.2).1]

lemma rpnonneg (n : ℕ) : 0 ≤ (Nat.cast : ℕ → ℝ) (pp n) := by apply Nat.cast_nonneg

-- 不等式条件から収束についての結論を導くところを抽象化する？
section

-- variable (seq : ℕ → ℕ) (h : (n : ℕ) → (seq n) ^ 3 ≤ seq (n + 1)) (h' : (n : ℕ) → (npos : 0 < n) → seq (n + 1) < ((seq n) + 1) ^ 3 - 1) (seq1gt1 : 1 < seq 1)
variable (seq : ℕ → ℕ) (h' : (n : ℕ) → seq (n + 1) < ((seq n) + 1) ^ 3 - 1)

noncomputable def seq_left : (ℕ → ℕ) → (ℕ → ℝ) := fun seq n ↦ ((Nat.cast : ℕ → ℝ) (seq n)) ^ (1 / (Nat.cast : ℕ → ℝ) 3 ^ n)

noncomputable def seq_right : (ℕ → ℕ) → (ℕ → ℝ) := fun seq n ↦ ((Nat.cast : ℕ → ℝ) (seq n) + 1) ^ (1 / (Nat.cast : ℕ → ℝ) 3 ^ n)

lemma rseqnonneg (n : ℕ) : 0 ≤ (Nat.cast : ℕ → ℝ) (seq n) := by simp

lemma left_nonneg (n : ℕ) : 0 ≤ seq_left seq n := by rw [seq_left]; apply Real.rpow_nonneg (by linarith)

lemma left_gt_1 (seq1gt1 : 1 < seq 1) : 1 < seq_left seq 1 := by
  rw [seq_left]; simp; rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by simp) (by norm_num)]; simp;
  exact seq1gt1

lemma left_lt_right (n : ℕ) : (seq_left seq) n < (seq_right seq) n := by
  rw [seq_left, seq_right]
  apply Real.rpow_lt_rpow (by apply rseqnonneg) (by linarith) (by norm_num)

lemma mono_left (h : (n : ℕ) → (seq n) ^ 3 ≤ seq (n + 1)) : Monotone (seq_left seq) := by
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

lemma str_anti_right (n : ℕ) (npos : 0 < n) (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : seq_right seq (n + 1) < seq_right seq n := by
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
  have : (if n = 0 then seq (n + 1) ≤ (seq n + 1) ^ 3 - 1 else seq (n + 1) < (seq n + 1) ^ 3 - 1) := h'' n
  rw [if_neg (by linarith [npos])] at this
  exact this
  rw [← one_pow 3]
  apply pow_le_pow_left₀
  linarith
  simp

lemma anti_right (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : Antitone (seq_right seq) := by
  apply antitone_nat_of_succ_le
  intro n
  have : 0 < (3 : ℝ) ^ (n + 1) := by norm_num
  rw [← Real.rpow_le_rpow_iff (by apply Real.rpow_nonneg (by linarith [rpnonneg])) (by apply Real.rpow_nonneg (by linarith [rpnonneg])) this]
  rw [seq_right, seq_right]
  rw [← Real.rpow_mul (by linarith [rpnonneg]), ← Real.rpow_mul (by linarith [rpnonneg])]
  ring_nf
  field_simp
  have : (1 + (Nat.cast : ℕ → ℝ) (seq n)) ^ (OfNat.ofNat 3 : ℝ) = (Nat.cast : ℕ → ℝ) ((1 + (seq n)) ^ 3) := by
    simp
    rw [← Real.rpow_natCast]
    apply congrArg
    simp
  rw [this, add_comm, ← le_add_neg_iff_add_le, ← sub_eq_add_neg]
  have : OfNat.ofNat 1 = (Nat.cast : ℕ → ℝ) 1 := by simp
  rw [this, ← Nat.cast_sub, Nat.cast_le, add_comm, add_comm 1 (seq n)]
  have : (if n = 0 then seq (n + 1) ≤ (seq n + 1) ^ 3 - 1 else seq (n + 1) < (seq n + 1) ^ 3 - 1) := h'' n
  by_cases hn : n = 0
  · rw [if_pos hn] at this
    exact this
  · rw [if_neg hn] at this
    exact le_of_lt this
  rw [← one_pow 3]
  apply pow_le_pow_left₀
  linarith
  simp

lemma bdd_left (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : BddAbove (Set.range (seq_left seq)) := by
  use (seq_right seq) 0
  intro x hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  calc
    (seq_left seq) n ≤ (seq_right seq) n := le_of_lt (left_lt_right seq n)
    _ ≤ (seq_right seq) 0 := anti_right seq h'' (by norm_num)

lemma bdd_right (h : (n : ℕ) → (seq n) ^ 3 ≤ seq (n + 1)) : BddBelow (Set.range (seq_right seq)) := by
  use (seq_left seq) 0
  intro x hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  calc
    (seq_left seq) 0 ≤ (seq_left seq) n := mono_left seq h (by norm_num)
    _ ≤ (seq_right seq) n := le_of_lt (left_lt_right seq n)

noncomputable def left_lim : ℝ := sSup (Set.range (seq_left seq))

noncomputable def right_lim : ℝ := sInf (Set.range (seq_right seq))

lemma left_sup (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : IsLUB (Set.range (seq_left seq)) (left_lim seq) := Real.isLUB_sSup ⟨(seq_left seq) 1, by simp⟩ (bdd_left seq h'')

lemma left_le_sup (n : ℕ) (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : (seq_left seq) n ≤ left_lim seq := (left_sup seq h'').left ⟨n, rfl⟩

lemma left_lim_nonneg (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : 0 ≤ left_lim seq := by linarith [left_le_sup seq 1 h'', left_nonneg seq 1]

lemma left_lim_gt_1 (seq1gt1 : 1 < seq 1) (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : 1 < left_lim seq := by linarith [left_gt_1 seq seq1gt1, left_le_sup seq 1 h'']

lemma right_inf : IsGLB (Set.range (seq_right seq)) (right_lim seq) := Real.isGLB_sInf ⟨(seq_right seq) 1, by simp⟩ (bdd_right seq h)

lemma right_inf_lt (n : ℕ) (npos : 0 < n) (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : right_lim seq < (seq_right seq) n := by
  by_contra hyp; push_neg at hyp
  have : seq_right seq (n + 1) < seq_right seq n := by apply str_anti_right seq h''; linarith
  have : seq_right seq (n + 1) < right_lim seq := by linarith
  have : right_lim seq ≤ seq_right seq (n + 1) := by apply (right_inf seq h).left; use (n + 1)
  linarith

lemma left_sup_le_right_inf (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : left_lim seq ≤ right_lim seq := by
  by_contra hyp; push_neg at hyp
  rcases IsLUB.exists_between (left_sup seq h'') hyp with ⟨x, ⟨n, _⟩, h₁⟩
  rcases IsGLB.exists_between (right_inf seq h) h₁.left with ⟨y, ⟨m, _⟩, h₃⟩
  let k := max n m
  have : (seq_right seq) k ≤ (seq_right seq) m := anti_right seq h'' (le_max_right n m)
  have : (seq_left seq) n ≤ (seq_left seq) k := mono_left seq h (le_max_left n m)
  have : (seq_left seq) k < (seq_right seq) k := left_lt_right seq k
  linarith

lemma right_lim_nonneg (h : (n : ℕ) → (seq n) ^ 3 ≤ seq (n + 1)) (h'' : (n : ℕ) → (if n = 0 then seq (n + 1) ≤ ((seq n) + 1) ^ 3 - 1 else seq (n + 1) < ((seq n) + 1) ^ 3 - 1)) : 0 ≤ right_lim seq := by calc
  0 ≤ left_lim seq := by apply left_lim_nonneg seq h''
  _ ≤ right_lim seq := by apply left_sup_le_right_inf seq h h''

lemma left_pow_eq_seq (n : ℕ) : (Nat.cast : ℕ → ℝ) (seq n) ^ ((1 : ℝ) / 3 ^ n) = seq_left seq n := rfl

lemma left_le_sup_pow (n : ℕ) : (Nat.cast : ℕ → ℝ) (seq n) ≤ (left_lim seq) ^ (3 ^ n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_inv_le_iff_of_pos (by linarith) (left_lim_nonneg seq h'') (by norm_num)]
  field_simp
  rw [left_pow_eq_seq seq n]
  exact left_le_sup seq h'' n

lemma right_pow_eq_seq (n : ℕ) : ((Nat.cast : ℕ → ℝ) (seq n) + 1) ^ ((1 : ℝ) / 3 ^ n) = seq_right seq n := rfl

lemma right_inf_pow_lt (n : ℕ) (npos : 0 < n) (h : (n : ℕ) → (seq n) ^ 3 ≤ seq (n + 1)) : (right_lim seq) ^ (3 ^ n) < (Nat.cast : ℕ → ℝ) (seq n + 1) := by
  rw [← Real.rpow_natCast, ← Real.lt_rpow_inv_iff_of_pos _ (by linarith) (by norm_num)]
  field_simp
  rw [right_pow_eq_seq seq n]
  apply right_inf_lt seq h
  exact h''
  have : (if n = 0 then seq (n + 1) ≤ (seq n + 1) ^ 3 - 1 else seq (n + 1) < (seq n + 1) ^ 3 - 1) := h'' n
  rw [if_neg (by linarith [npos])] at this
  linarith [left_sup_le_right_inf seq h h'', left_lim_nonneg seq h'']
  apply right_lim_nonneg seq h h''

lemma left_floor_eq_seq (n : ℕ) (npos : 0 < n) (h : (n : ℕ) → (seq n) ^ 3 ≤ seq (n + 1)) : Nat.floor ((left_lim seq) ^ (3 ^ n)) = seq n := by
    rw [Nat.floor_eq_iff]
    constructor
    · exact left_le_sup_pow seq h'' n
    · calc
        (left_lim seq) ^ (3 ^ n) ≤ (right_lim seq) ^ (3 ^ n) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast]
          apply (Real.rpow_le_rpow_iff (left_lim_nonneg seq h'') (by linarith [left_sup_le_right_inf seq h h'', left_lim_nonneg seq h'']) (by norm_num)).2 (left_sup_le_right_inf seq h h'')
        _ < (Nat.cast : ℕ → ℝ) (seq n + 1) := right_inf_pow_lt seq h h'' n npos
        _ = seq n + 1 := by simp
    rw [← Real.rpow_natCast]
    apply Real.rpow_nonneg (left_lim_nonneg seq h'')

end

lemma aux' (n : ℕ) : if n = 0 then pp (n + 1) ≤ (pp n + 1) ^ 3 - 1 else pp (n + 1) < (pp n + 1) ^ 3 - 1 := by
  split_ifs
  · exact le_of_lt (hpp n).right.right.left
  · exact (hpp n).right.right.left

theorem exists_Mills : ∃ A : ℝ, Mills A := by
  have : 1 < pp 1 := by rw [pp]; linarith [(pp' 1).property, BHP_const_nat_ge2]
  use (left_lim pp)
  constructor
  · exact (by linarith [(left_gt_1 pp this), (left_le_sup pp (fun n ↦ aux' n) 1)])
  · intro k h
    rw [left_floor_eq_seq pp (fun n ↦ (hpp n).left) (fun n ↦ aux' n) k, ← Nat.succ_pred_eq_of_pos h]
    exact (hpp k.pred).right.right.right
    exact h
