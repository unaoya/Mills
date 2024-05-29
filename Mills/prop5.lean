import Mills.Defs
import Mills.lem6
import Mills.sequence

open NNReal

lemma prop5 : ∃ k₀ : ℕ+, k₀ > 1 ∧ ∀ k, k₀ ≤ k → pnat_cube (Mills_seq A k) ≤ Mills_seq A (k + 1) ∧ Mills_seq A (k + 1) ≤ pnat_cube (Mills_seq A k) + pn_pow_nnr (Mills_seq A k) (3 * θ) := by
  by_contra h
  push_neg at h
  rcases h BHP_const_pnat sorry with ⟨k, hk₀, hk₁⟩
  have h₀ : ↑↑(pnat_cube (Mills_seq A k)) + pn_pow_nnr (Mills_seq A k) (3 * θ) < ↑↑(Mills_seq A (k + 1)) := by
    sorry
  have h₁ : ∃ q : ℕ+, Nat.Prime q ∧ pnat_cube (Mills_seq A k) ≤ q ∧ q ≤ (pnat_cube (Mills_seq A k)) + pn_pow_nnr (Mills_seq A k) (3 * θ) ∧ q < pnat_cube (Mills_seq A k + 1) := by
    sorry
  rcases h₁ with ⟨q, hq₀, hq₁, hq₂, hq₃⟩
  have : q < Mills_seq A (k + 1) := by sorry
  have : ∃ qq : ℕ+ → ℕ+, qq (k + 1) = q ∧ sorry := by sorry
  rcases this with ⟨qq, hqq⟩
  let B := left_lim qq
  have : B < A := by sorry
