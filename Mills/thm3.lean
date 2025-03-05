import Mathlib.Data.PNat.Find
import Mills.Defs
import Mills.sequence

open Filter Topology NNReal

structure GoodPrimeSeq where
  seq : ℕ+ → ℕ+
  left (n : ℕ+) : pnat_cube (seq n) ≤ seq (n + 1)
  right (n : ℕ+) : seq (n + 1) < pnat_cube ((seq n) + 1) - 1
  prime (n : ℕ+) : Nat.Prime (seq n)

namespace GoodPrimeSeq

def toGoodSeq (seq : GoodPrimeSeq) : GoodSeq :=
{
  seq := seq.seq
  h := seq.left
  h' := seq.right
  seq1gt1 := Nat.Prime.one_lt (seq.prime 1)
}

noncomputable
def left_seq (seq : GoodPrimeSeq) : ℕ+ → ℝ≥0 :=
  fun n => cube_pow_rt (seq.seq n) n

noncomputable
def right_seq (seq : GoodPrimeSeq) : ℕ+ → ℝ≥0 :=
  fun n => cube_pow_rt (seq.seq n + 1) n

def left_lim : ℝ≥0 := sorry

def right_lim : ℝ≥0 := sorry

lemma left_lim_le_right_lim : left_lim ≤ right_lim := sorry

lemma left_lim_ub (seq : GoodPrimeSeq) (n : ℕ+) : seq.left_seq n < left_lim := sorry

lemma right_lim_lb (seq : GoodPrimeSeq) (n : ℕ+) : right_lim < seq.right_seq n := sorry

end GoodPrimeSeq


lemma aux (x : ℝ) (xpos : 1 < x) : x ^ 3 + x ^ 2 ≤ (x + 1) ^ 3 - 1 := by nlinarith

-- 定理3の冒頭の不等式。これは一般的に成り立つ。似た話を後でも使う？
lemma aux_ineq_in_thm3 (x : ℝ≥0) (xgt1 : 1 < x) :
    x.rpow 3 + x.rpow (3 * θ).toReal < (x + 1).rpow 3 - 1 := by
  have : (3 * θ).toReal < 2 := by rw [θ]; norm_num;
  calc
    x.rpow 3 + x.rpow (3 * θ).toReal < x.rpow 3 + x.rpow 2 := by
      apply add_lt_add_left (Real.rpow_lt_rpow_of_exponent_lt xgt1 this)
    _ = x ^ 3 + x ^ 2 := by simp
    _ ≤ (x + 1) ^ 3 - 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_sub _]; simp
      exact aux x.val xgt1
      calc
        1 ≤ x + 1 := by apply le_add_of_nonneg_left; simp
        _ ≤ (x + 1) ^ 3 := by apply le_self_pow; simp; simp
    _ = (x + 1).rpow 3 - 1 := by simp

def Step : ℕ+ → ℕ+ → Prop := fun p q =>
  pnat_cube p ≤ q ∧
  q ≤ p ^ 3 + (p : ℝ).rpow (3 * θ) ∧
  q < pnat_cube (p + 1) - 1 ∧
  Nat.Prime q

noncomputable instance (m : ℕ+) : DecidablePred (Step m) := fun x ↦ by
  exact Classical.propDecidable (Step m x)

lemma Step_aux (n m : ℕ+) (h : pnat_cube n ≤ m) (h' : BHP_const_pnat ≤ n) :
    BHP_const_pnat ≤ m := by
  calc
    BHP_const_pnat ≤ n := h'
    _ ≤ pnat_cube n := by
      unfold pnat_cube
      simp
      sorry
    _ ≤ m := h

lemma Stepex : ∀ p : ℕ+, BHP_const_pnat ≤ p → ∃ (q : ℕ+), Step p q := by sorry

def NgeBHP : Type := {n : ℕ+ // BHP_const_pnat ≤ n}

structure Step' (p q : NgeBHP) where
  h₀ : pnat_cube p.val ≤ q.val
  h₁ : q.val ≤ p.val ^ 3 + (p.val : ℝ).rpow (3 * θ)
  h₂ : q.val < pnat_cube (p.val + 1) - 1
  h₃ : Nat.Prime q.val

lemma Stepex₀ (p : NgeBHP) : ∃ (q : NgeBHP), Step' p q := by sorry

lemma Stepex'' (p : NgeBHP) : ∃ (q : ℕ+), Step p.val q ∧ BHP_const_pnat ≤ q := by
  obtain ⟨q, hq⟩ := Stepex₀ p
  use q.val
  constructor
  · exact ⟨hq.h₀, hq.h₁, hq.h₂, hq.h₃⟩
  · exact q.property

noncomputable
def pp' (p₀ : NgeBHP) : ℕ → NgeBHP
  | 0 => p₀
  | n + 1 => ⟨PNat.find (Stepex'' (pp' p₀ n)), (PNat.find_spec (Stepex'' (pp' p₀ n))).2⟩

noncomputable
def pp'' (p₀ : NgeBHP) : ℕ → NgeBHP
  | 0 => p₀
  | n + 1 => Classical.choose (Stepex₀ (pp'' p₀ n))

lemma hpp'' (p₀ : NgeBHP) (k : ℕ) : Step' (pp'' p₀ k) (pp'' p₀ (k + 1)) := by
  exact (Classical.choose_spec (Stepex₀ (pp'' p₀ k)))

-- BHP定数より大きな素数を与えたら、そこからGPSを作る
noncomputable
def GPS_construction (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) : GoodPrimeSeq :=
{
  seq (n : ℕ+) := (pp'' ⟨p₀, h⟩ n.natPred).val
  left := sorry
  right := sorry
  prime := sorry
}

noncomputable
def pp (p₀ : NgeBHP) : ℕ+ → ℕ+ := λ n => (pp' p₀ n.natPred).val

lemma hpp' (p₀ : NgeBHP) : ∀ k : ℕ, Step (pp' p₀ k).val (pp' p₀ (k + 1)).val := by
  intro k
  exact (PNat.find_spec (Stepex'' (pp' p₀ k))).1

lemma hpp (p₀ : NgeBHP) : ∀ k : ℕ+, Step (pp p₀ k) (pp p₀ (k + 1)) := by
  intro k
  unfold pp
  have : (k + 1).natPred = k.natPred + 1 := by
    simp
    exact rfl
  rw [this]
  apply hpp' p₀ k.natPred

lemma left_ineq (p₀ : NgeBHP) (n : ℕ+) : pnat_cube (pp p₀ n) ≤ pp p₀ (n + 1) := by
  apply (hpp p₀ n).left

lemma right_ineq (p₀ : NgeBHP) (n : ℕ+) : pp p₀ (n + 1) < pnat_cube (pp p₀ n + 1) - 1 := by
  apply (hpp p₀ n).right.right.left

lemma pp1_gt_1 (p₀ : NgeBHP) : 1 < pp p₀ 1 := by
  calc
    1 < 2 := by simp
    _ ≤ BHP_const_pnat := BHP_const_pnat_ge2
    _ ≤ p₀.val := p₀.property
    _ = pp p₀ 1 := rfl

lemma ppn_prime (p₀ : NgeBHP) (n : ℕ+) : Nat.Prime (pp p₀ n) := by
--    apply (hpp p₀ h n).right.right.right
  sorry

theorem exists_Mills : ∃ A : ℝ≥0, Mills A := by
  set p := (GPS_construction BHP_const_pnat (by simp)).toGoodSeq
  use (left_lim p)
  rw [Mills]
  constructor
  · apply left_lim_gt_1
  · intro n
    have : Nat.floor ((left_lim p).pnpow (pnat_cube n)) = p.seq n := by
      apply left_floor_eq_seq p
    rw [Mills_seq]
    sorry
--    apply ppn_prime

theorem W_nonempty : W.Nonempty := exists_Mills

def W_real := { x | ∃ A : ℝ≥0, Mills A ∧ x = A.val }

theorem W_real_nonempty : W_real.Nonempty := sorry
