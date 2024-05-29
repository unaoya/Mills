import Mathlib.Data.PNat.Find
import Mills.Defs
import Mills.sequence

open Filter Topology NNReal

lemma aux (x : ℝ) (xpos : 0 < x) : x ^ 3 + x ^ 2 ≤ (x + 1) ^ 3 - 1 := by nlinarith

lemma aux' (x : ℝ≥0) (xpos : 0 < x) : x ^ 3 + x ^ 2 ≤ (x + 1) ^ 3 - 1 := by
  rw [← NNReal.coe_le_coe, NNReal.coe_sub _]; simp
  exact aux x.val xpos
  calc
    1 ≤ x + 1 := by apply le_add_of_nonneg_left; simp
    _ ≤ (x + 1) ^ 3 := by apply le_self_pow; simp; simp

-- 定理3の冒頭の不等式。これは一般的に成り立つ。似た話を後でも使う？
lemma aux_ineq_in_thm3 (x : ℝ≥0) (xgt1 : 1 < x.val) : x.rpow 3 + x.rpow (3 * θ).toReal < (x + 1).rpow 3 - 1 := by
  have : (3 * θ).toReal < 2 := by rw [θ]; norm_num;
  calc
    x.rpow 3 + x.rpow (3 * θ).toReal < x.rpow 3 + x.rpow 2 := by apply add_lt_add_left (Real.rpow_lt_rpow_of_exponent_lt xgt1 this)
    _ = x ^ 3 + x ^ 2 := by simp
    _ ≤ (x + 1) ^ 3 - 1 := by apply aux'; nlinarith
    _ = (x + 1).rpow 3 - 1 := by simp

def Step : ℕ+ → ℕ+ → Prop := fun p q =>
  pnat_cube p ≤ q ∧ q ≤ p ^ 3 + (p : ℝ).rpow (3 * θ) ∧ q < pnat_cube (p + 1) - 1 ∧ Nat.Prime q

noncomputable instance (m : ℕ+) : DecidablePred (Step m) := fun _ ↦ And.decidable

lemma Step_aux (n m : ℕ+) (h : pnat_cube n ≤ m) (h' : BHP_const_pnat ≤ n) : BHP_const_pnat ≤ m := by sorry

lemma Stepex : ∀ p : ℕ+, BHP_const_pnat ≤ p → ∃ (q : ℕ+), Step p q := by sorry

def NgeBHP : Type := {n : ℕ+ // BHP_const_pnat ≤ n}

noncomputable def pp' (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) : ℕ → NgeBHP
| 0 => ⟨p₀, h⟩
| n + 1 => ⟨PNat.find (Stepex (pp' p₀ h n).val (pp' p₀ h n).property),
            Step_aux (pp' p₀ h n).val (PNat.find (Stepex (pp' p₀ h n).val (pp' p₀ h n).property)) (PNat.find_spec (Stepex (pp' p₀ h n).val (pp' p₀ h n).property)).left (pp' p₀ h n).property⟩

noncomputable def pp (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) : ℕ+ → ℕ+ := λ n => (pp' p₀ h n.natPred).val

lemma hpp' (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) : ∀ k : ℕ, Step (pp' p₀ h k).val (pp' p₀ h (k + 1)).val := by intro k; exact PNat.find_spec (Stepex (pp' p₀ h k).val (pp' p₀ h k).property)

lemma hpp (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) : ∀ k : ℕ+, Step (pp p₀ h k) (pp p₀ h (k + 1)) := by intro k; sorry

lemma left_ineq (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) (n : ℕ+) : pnat_cube (pp p₀ h n) ≤ pp p₀ h (n + 1) := by
  apply (hpp p₀ h n).left

lemma right_ineq (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) (n : ℕ+) : pp p₀ h (n + 1) < pnat_cube (pp p₀ h n + 1) - 1 := by
  apply (hpp p₀ h n).right.right.left

lemma pp1_gt_1 (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) : 1 < pp p₀ h 1 := by sorry

lemma ppn_prime (p₀ : ℕ+) (h : BHP_const_pnat ≤ p₀) (n : ℕ+) : Nat.Prime (pp p₀ h n) := by
--    apply (hpp p₀ h n).right.right.right
  sorry

theorem exists_Mills : ∃ A : ℝ≥0, Mills A := by
  set p := pp BHP_const_pnat (by simp)
  use (left_lim p)
  rw [Mills]
  constructor
  · apply left_lim_gt_1 _ _ _
    apply pp1_gt_1
    apply left_ineq
    apply right_ineq
  · intro n
    have : Nat.floor ((left_lim p).pnpow (pnat_cube n)) = p n := by
      apply left_floor_eq_seq _ _ _
      apply pp1_gt_1
      apply left_ineq
      apply right_ineq
    rw [Mills_seq]
    rw [this]
    apply ppn_prime

theorem W_nonempty : W.Nonempty := exists_Mills

def W_real := { x | ∃ A : ℝ≥0, Mills A ∧ x = A.val }

theorem W_real_nonempty : W_real.Nonempty := sorry
