import Mills.Defs

open Filter Topology NNReal

def NNReal.pnpow (x : ℝ≥0) (n : ℕ+) : ℝ≥0 := x ^ n.val

instance : HPow ℝ≥0 ℕ+ ℝ≥0 := ⟨NNReal.pnpow⟩

def pnat_cube (m : ℕ+) : ℕ+ := ⟨Nat.pow 3 m, Nat.pow_pos (by norm_num)⟩

noncomputable
def cube_pow_rt (n k : ℕ+) : ℝ≥0 := (n : ℝ≥0).rpow (1 / (pnat_cube k) : ℝ≥0)

lemma cpr_lt {n m : ℕ+} (k : ℕ+) (h : n < m) : cube_pow_rt n k < cube_pow_rt m k := by sorry

lemma pnat_gt_succ (n : ℕ+) : n < n + 1 := by
  rw [← PNat.coe_lt_coe]; simp

lemma pnat_cube_le (n : ℕ+) : n ≤ pnat_cube n := by sorry

lemma pnpow_le_iff {x y : ℝ≥0} (n : ℕ+) : x ≤ y ↔ x ^ n ≤ y ^ n := by sorry

lemma cpr_pnp (k n : ℕ+) : (cube_pow_rt k n) ^ (pnat_cube n) = k := by sorry

lemma pnpow_lt_iff {x y : ℝ≥0} (n : ℕ+) : x < y ↔ x ^ n < y ^ n := by sorry

lemma cpr_pnp' (k n : ℕ+) : (cube_pow_rt k n) ^ (pnat_cube (n + 1)) = pnat_cube k := by sorry

lemma cube_le (n m : ℕ+) (x : ℝ≥0) : n ≤ x ^ (pnat_cube m) ↔ cube_pow_rt n m ≤ x := sorry

lemma cube_lt (n m : ℕ+) (x : ℝ≥0) : x ^ (pnat_cube m) < n ↔ x < cube_pow_rt n m := sorry

lemma pnpow_le {a b : ℝ≥0} (n : ℕ+) (h : a ≤ b) : a ^ n ≤ b ^ n := by sorry

lemma pred_succ (n : ℕ+) (ngt1 : 1 < n) : n - 1 + 1 = n.natPred.succPNat := by
  rw [PNat.add_one]
  congr
  rw [PNat.sub_coe]
  apply dif_pos ngt1

lemma monotone_iff_comp_orderiso {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    (h : α ≃o β) (f : β → γ) : Monotone f ↔ Monotone (f.comp h) := by
  constructor
  · intro hf
    apply Monotone.comp hf
    exact OrderIso.monotone h
  · intro hf
    have : f = (f.comp h).comp h.symm := by
      ext x
      simp
    rw [this]
    apply Monotone.comp hf
    exact OrderIso.monotone h.symm

lemma monotone_pnat_of_le_succ {α : Type*} {f : ℕ+ → α} [Preorder α] (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f := by
  rw [monotone_iff_comp_orderiso (OrderIso.pnatIsoNat).symm]
  simp
  have : ∀ n, (f ∘ Nat.succPNat) n ≤ (f ∘ Nat.succPNat) (n + 1) := by
    intro n
    simp
    apply hf
  exact monotone_nat_of_le_succ this

lemma strictAnti_pnat_of_succ_lt {f : ℕ+ → ℝ≥0} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  sorry
--  Nat.rel_of_forall_rel_succ_of_le (· ≤ ·) hf

-- 不等式条件から収束についての結論を導くところを抽象化する
-- variableをやめて、定理としてかく

-- $p_k^3 ≤ p_{k+1}$を満たす数列に対し、$q_k = p_k^{1/(3^k)}$とすると、
-- これは上に有界な単調増加列になり、極限が存在する。

-- $p_{k+1} < p_k^3 - 1$を満たす数列に対し、$r_k = (p_k + 1)^{1/(3^k)}$とすると、
-- これは下に有界な狭義単調列になり、極限が存在する。

-- 二つの条件を満たす数列に対し、任意の$k$で$q_k ≤ r_k$が成り立ち、極限の不等式が成り立つ。

-- 初項が$1$より大きいとき、極限も$1$より大きい。

structure GoodSeq where
  seq : ℕ+ → ℕ+
  seq1gt1 : 1 < seq 1
  left (n : ℕ+) : pnat_cube (seq n) ≤ seq (n + 1)
  right (n : ℕ+) : seq (n + 1) < pnat_cube ((seq n) + 1) - 1

namespace GoodSeq

instance : CoeFun GoodSeq (fun _ => ℕ+ → ℕ+) := ⟨GoodSeq.seq⟩

variable (seq : GoodSeq)

lemma mono_seq : Monotone seq := by
  apply monotone_pnat_of_le_succ
  intro n
  calc
    seq n ≤ pnat_cube (seq n) := pnat_cube_le (seq n)
    _ ≤ seq (n + 1) := seq.left n

noncomputable
def seq_left (n : ℕ+): ℝ≥0 := cube_pow_rt (seq n) n

lemma left_gt_1 : 1 < seq.seq_left 1 := by
  apply one_lt_rpow _ (by simp)
  simp
  exact seq.seq1gt1

lemma mono_left : Monotone seq.seq_left := by
  apply monotone_pnat_of_le_succ
  intro n
  rw [seq_left, seq_left, pnpow_le_iff (pnat_cube (n + 1)), cpr_pnp (seq (n + 1)) (n + 1)]
  rw [cpr_pnp' (seq n) n]
  simp
  exact seq.left n

noncomputable
def seq_right (n : ℕ+) : ℝ≥0 := cube_pow_rt (seq n + 1) n

lemma str_anti_right : StrictAnti seq.seq_right := by
  apply strictAnti_pnat_of_succ_lt
  intro n
  rw [seq_right, seq_right, pnpow_lt_iff (pnat_cube (n + 1)), cpr_pnp (seq (n + 1) + 1) (n + 1), cpr_pnp' (seq n + 1) n, Nat.cast_lt, PNat.coe_lt_coe]
  calc
    seq (n + 1) + 1 < pnat_cube (seq n + 1) - 1 + 1 := by apply add_lt_add_right; apply seq.right
    _ = (pnat_cube (seq n + 1)).natPred.succPNat := by
      apply pred_succ
      calc
        1 < seq 1 := seq.seq1gt1
        _ ≤ seq n := by apply mono_seq seq; simp
        _ < seq n + 1 := by apply pnat_gt_succ
        _ ≤ pnat_cube (seq n + 1) := by apply pnat_cube_le
    _ = pnat_cube (seq n + 1) := by apply PNat.succPNat_natPred

lemma anti_right : Antitone seq.seq_right := StrictAnti.antitone seq.str_anti_right

lemma left_lt_right (n : ℕ+) : seq.seq_left n < seq.seq_right n := by
  apply cpr_lt
  apply pnat_gt_succ

lemma bdd_left : BddAbove (Set.range seq.seq_left) := by
  use seq.seq_right 1
  intro x hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  calc
    seq.seq_left n ≤ seq.seq_right n := le_of_lt (left_lt_right seq n)
    _ ≤ seq.seq_right 1 := by apply seq.anti_right; simp

lemma bdd_right : BddBelow (Set.range seq.seq_right) := by
  use seq.seq_left 1
  intro x hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  calc
    seq.seq_left 1 ≤ seq.seq_left n := seq.mono_left (by norm_num)
    _ ≤ seq.seq_right n := le_of_lt (left_lt_right seq n)

/--
サーベイの$A$
-/
noncomputable
def left_lim : ℝ≥0 := sSup (Set.range seq.seq_left)

/--
サーベイの$A'$
-/
noncomputable
def right_lim : ℝ≥0 := sInf (Set.range seq.seq_right)

lemma left_sup : IsLUB (Set.range seq.seq_left) (left_lim seq) := by
  apply isLUB_csSup
  use seq.seq_left 1
  use 1
  exact bdd_left seq

lemma left_le_sup (n : ℕ+) : seq.seq_left n ≤ left_lim seq := (left_sup seq).left ⟨n, rfl⟩

lemma left_lim_nonneg : 0 ≤ left_lim seq := by simp

lemma left_lim_gt_1 : 1 < left_lim seq := by calc
  1 < seq.seq_left 1 := seq.left_gt_1
  _ ≤ left_lim seq := left_le_sup seq 1

lemma right_inf : IsGLB (Set.range seq.seq_right) (right_lim seq) := by
  apply isGLB_csInf
  use seq.seq_right 1
  use 1
  exact bdd_right seq

lemma right_inf_lt (n : ℕ+) : right_lim seq < seq.seq_right n := by
  by_contra hyp; push_neg at hyp
  apply ne_of_lt (a := seq.seq_right (n + 1)) (b := seq.seq_right (n + 1))
  · apply lt_of_lt_of_le (b := right_lim seq)
    · calc
        seq.seq_right (n + 1) < seq.seq_right n := by
          apply seq.str_anti_right; simp [← PNat.coe_lt_coe]
        _ ≤ right_lim seq := hyp
    · apply (seq.right_inf).left; use (n + 1)
  · rfl

/--
$A \leq A'$であること
-/
lemma left_sup_le_right_inf : left_lim seq ≤ right_lim seq := by
  by_contra hyp; push_neg at hyp
  rcases IsLUB.exists_between (left_sup seq) hyp with ⟨x, ⟨n, hx⟩, h₁⟩
  rcases IsGLB.exists_between (right_inf seq) h₁.left with ⟨y, ⟨m, hy⟩, ⟨_, h₃⟩⟩
  let k := max n m
  have h₄ : seq.seq_left n < seq.seq_right m := by calc
    seq.seq_left n ≤ seq.seq_left k := by apply seq.mono_left; exact le_max_left n m
    _ < seq.seq_right k := left_lt_right seq k
    _ ≤ seq.seq_right m := by apply seq.anti_right; exact (le_max_right n m)
  rw [← hx, ← hy] at h₃
  apply not_lt_of_lt h₄ h₃

-- lemma left_pow_eq_seq (n : ℕ+) : cube_pow_rt (seq n) n = seq.seq_left n := rfl

/--
$p_n \leq A^{3^n}$であること
-/
lemma left_le_sup_pow (n : ℕ+) : (seq n) ≤ (left_lim seq) ^ (pnat_cube n) := by
  rw [cube_le]
  apply left_le_sup seq

-- lemma right_pow_eq_seq (n : ℕ+) : cube_pow_rt (seq n + 1) n = seq.seq_right n := rfl

lemma right_inf_pow_lt (n : ℕ+) : (right_lim seq) ^ (pnat_cube n) < (seq n + 1) := by
  have : @Nat.cast ℝ≥0 _ ((seq n + 1).val) = seq n + 1 := by simp
  rw [← this, cube_lt]
  apply right_inf_lt seq

/--
$\lfloor A^{3^n} \rfloor = p_n$であること。
-/
theorem left_floor_eq_seq (n : ℕ+) : Nat.floor ((left_lim seq) ^ (pnat_cube n)) = seq n := by
    rw [Nat.floor_eq_iff]
    constructor
    · exact left_le_sup_pow seq n
    · calc
        (left_lim seq) ^ (pnat_cube n) ≤ (right_lim seq) ^ (pnat_cube n) := by
          apply pnpow_le (pnat_cube n) (left_sup_le_right_inf seq)
        _ < (seq n + 1) := right_inf_pow_lt seq n
        _ = seq n + 1 := by simp
    simp
