import Init.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open Filter Topology NNReal

-- noncomputableとは？

noncomputable def θ : ℝ≥0 := 0.525

-- notationも導入する？

noncomputable def NNReal.pnpow (x : ℝ≥0) (n : ℕ+) : ℝ≥0 := x ^ n.val

def pnat_cube (m : ℕ+) : ℕ+ := ⟨Nat.pow 3 m, Nat.pow_pos (by norm_num)⟩

lemma pnat_cube_succ (m : ℕ+) : pnat_cube (m + 1) = pnat_cube m * 3 := by
  sorry

noncomputable def Mills_seq (x : ℝ≥0) (n : ℕ+) : ℕ := Nat.floor (x.pnpow (pnat_cube n))

def Mills (x : ℝ≥0) : Prop := 1 < x ∧ ∀ n : ℕ+, Nat.Prime (Mills_seq x n)

def W := {x | Mills x}

noncomputable def A : ℝ≥0 := sInf W

-- 3 ^ n のところも型をきちんと決めておいたほうがいいかも
-- 3 ^ n なのか 3 ^ n.valなのか
lemma Mills_seq_ge_2 (x : ℝ≥0) (n : ℕ+) (h : Mills x) : 2 ≤ Mills_seq x n := (Nat.prime_def_lt.1 (h.right n)).1

def Mills_lb (x : ℝ≥0) (h : Mills x) : 2 ≤ x.pnpow 3 := by
  have h₁ : 2 ≤ Mills_seq x 1 := Mills_seq_ge_2 x 1 h
  dsimp [Mills_seq] at h₁
  have h₂ : Nat.floor (x.pnpow 3) ≤ x.pnpow 3 := by apply Nat.floor_le; simp
  sorry

-- lemma hh₁ : IsGLB W (sInf W) := Real.is_glb_sInf W exists_Mills ⟨1, fun _ ha ↦ le_of_lt ha.1⟩

-- lemma A_lb : ∀ B ∈ W, A ≤ B := fun _ hB ↦ hh₁.left hB

-- Wのinfが1より大きいことを示す
lemma Mills_gt_one : 1 < A := by
  by_contra h; push_neg at h
  have h₀ : ∃ x ∈ W, x < 1.1 := by sorry --infなことを使う
  obtain ⟨x, hx, hlt⟩ := h₀
  have h₁ : x.pnpow 3 < 2 := by sorry --計算
  have h₂ : 2 ≤ x.pnpow 3 := by apply Mills_lb x hx
  have : (2 : ℝ≥0) < 2 := by apply lt_of_le_of_lt h₂ h₁
  sorry

axiom BHP : ∃ (x₀ : ℝ≥0), 2 ≤ x₀ ∧ ∀ (x : ℕ+), x ≥ x₀ → ∃ (p : ℕ+), (x ≤ p ∧ p ≤ x + (x : ℝ).rpow ^ θ.toReal ∧ Nat.Prime p)

noncomputable def BHP_const : ℝ≥0 := Classical.choose BHP

lemma BHP_const_ge2 : 2 ≤ BHP_const := (Classical.choose_spec BHP).left

noncomputable def BHP_const_nat : ℕ := Nat.ceil BHP_const

lemma BHP_const_nat_ge2 : 2 ≤ BHP_const_nat := by
  have : Nat.ceil ((Nat.cast : ℕ → ℝ) 2) ≤ Nat.ceil BHP_const := Nat.ceil_le_ceil 2 BHP_const BHP_const_ge2
  rw [Nat.ceil_natCast] at this
  exact this

-- lemma BHP_const_nat_BHP : ∀ x : ℕ, BHP_const_nat ≤ x → ∃ (p : ℕ), (x ≤ p ∧ p ≤ x + ((Nat.cast : ℕ → ℝ) x) ^ θ ∧ Nat.Prime p) := by
--   intro x hx
--   have : BHP_const ≤ x := by calc
--     BHP_const ≤ BHP_const_nat := by apply Nat.le_ceil
--     _ ≤ x := Nat.cast_le.2 hx
--   apply (Classical.choose_spec BHP).right
--   apply this
