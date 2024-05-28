import Mills.Defs

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

lemma prime_seq : ∃ (p : ℕ+ → ℕ+), ∀ n, Nat.Prime (p n) ∧ pnat_cube (p n) ≤ p (n + 1) ∧ p (n + 1) ≤ pnat_cube (p n + 1) - 1 := by sorry

theorem exists_Mills : ∃ A : ℝ≥0, Mills A := by sorry
/-
  have : 1 < pp 1 := by rw [pp]; linarith [(pp' 1).property, BHP_const_nat_ge2]
  use (left_lim pp)
  constructor
  · exact (by linarith [(left_gt_1 pp this), (left_le_sup pp (fun n ↦(hpp n).right.right.left) 1)])
  · intro k h
    rw [left_floor_eq_seq pp (fun n ↦ (hpp n).left) (fun n ↦ (hpp n).right.right.left) k, ← Nat.succ_pred_eq_of_pos h]
    exact (hpp k.pred).right.right.right
-/

theorem W_nonempty : W.Nonempty := exists_Mills

def W_real := { x | ∃ A : ℝ≥0, Mills A ∧ x = A.val }

theorem W_real_nonempty : W_real.Nonempty := sorry
