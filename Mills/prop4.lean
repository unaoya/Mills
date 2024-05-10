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

import Mills.Defs

open Filter Topology NNReal

def add_a_pow_k (a : ℝ) (k : ℕ) : ℝ → ℝ := (fun x : ℝ ↦ x ^ k) ∘ (fun x : ℝ ↦ a + x)

lemma h'' (a : ℝ) (k : ℕ) : Tendsto (fun n : ℕ ↦ (a + 1 / n) ^ k) atTop (𝓝 (a ^ k)) := by
  have : (fun n : ℕ ↦ (a + 1 / n ) ^ k) = add_a_pow_k a k ∘ (fun n : ℕ ↦ (n : ℝ)⁻¹) := by funext; rw [add_a_pow_k]; simp
  rw [this]
  have : Tendsto (add_a_pow_k a k) (𝓝 0) (𝓝 (add_a_pow_k a k 0)) := Continuous.tendsto (Continuous.comp (continuous_pow k) (continuous_add_left a)) 0
  simp [add_a_pow_k] at this
  apply tendsto_nhds_iff_seq_tendsto.mp this
  exact tendsto_inverse_atTop_nhds_zero_nat

lemma h''' (f : ℕ → ℝ) (a M : ℝ) (h : Tendsto f atTop (𝓝 a)) (h' : a < M) : ∃ N, ∀ n, N ≤ n → f n < M := by
  rcases (tendsto_atTop_nhds.mp h {x | x < M} h' (isOpen_gt' M)) with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ hN n hn⟩

lemma exist_n (a M : ℝ) (k : ℕ) (h : a ^ k < M) : ∃ n : ℕ, n > 0 ∧ (a + 1 / n) ^ k < M := by
  let f := fun n : ℕ ↦ (a + 1 / n) ^ k
  rcases h''' f (a ^ k) M (h'' a k) h with ⟨n, hn⟩
  exact ⟨n + 1, ⟨by linarith, hn (n + 1) (by linarith)⟩⟩

theorem Mills_exists : Mills A := by
  have h (k : ℕ) (hk : 0 < k) : Nat.Prime (Nat.floor (A ^ (3 ^ k))) := by
    let M := Nat.floor (A ^ (3 ^ k)) + 1
    have h₂ : A ^ (3 ^ k) < M := by dsimp [M]; apply Nat.lt_succ_floor (A ^ (3 ^ k))
    rcases exist_n A M (3 ^ k) h₂ with ⟨N, hN₁, hN₂⟩
    have h₁ (n : ℕ) (hn : n > 0) : ∃ B ∈ W, A ≤ B ∧ B < A + 1 / n := by
      have : 0 < (1 : ℝ) / n := by norm_num [hn]
      rcases Real.lt_sInf_add_pos exists_Mills this with ⟨B, hB₁, hB₂⟩
      exact ⟨B, ⟨hB₁, A_lb B hB₁, hB₂⟩⟩
    rcases h₁ N hN₁ with ⟨B, hB₁, _, hB₂⟩ -- むだ？上と同様
    have h₄ : Nat.floor (A ^ (3 ^ k)) ≤ B ^ (3 ^ k) := by linarith [floor_le A (3 ^ k) (by linarith [Mills_gt_one]), pow_le_left A B (3 ^ k) (by linarith [Mills_gt_one]) (A_lb B hB₁)]
    have h₅ : B ^ (3 ^ k) < ↑M := by linarith [pow_lt_left B (A + 1 / N) (3 ^ k) (by norm_num) hB₁.left hB₂]
    have h₆ : Nat.floor (A ^ (3 ^ k)) = Nat.floor (B ^ (3 ^ k)) := by
      apply floor_eq A B (3 ^ k) (by linarith [hB₁.left]) ⟨h₄, _⟩
      simp [M] at h₅
      exact h₅
    rw [h₆]
    exact hB₁.right k hk
  exact ⟨Mills_gt_one, h⟩
