import Mills.Defs
import Mills.thm3

open Filter Topology NNReal

lemma lim_add_n_inv_pow_k (a : ℝ) (k : ℕ) : Tendsto (fun n : ℕ ↦ (a + 1 / n) ^ k) atTop (𝓝 (a ^ k)) := by
  set add_a_pow_k := (fun x : ℝ ↦ x ^ k) ∘ (fun x : ℝ ↦ a + x) with add_a_pow_k_def
  have : (fun n : ℕ ↦ (a + 1 / n) ^ k) = add_a_pow_k ∘ (fun n : ℕ ↦ (n : ℝ)⁻¹) := by funext; rw [add_a_pow_k_def]; simp
  rw [this]
  have : Tendsto add_a_pow_k (𝓝 0) (𝓝 (add_a_pow_k 0)) := Continuous.tendsto (Continuous.comp (continuous_pow k) (continuous_add_left a)) 0
  simp [add_a_pow_k] at this
  apply tendsto_nhds_iff_seq_tendsto.mp this
  exact tendsto_inverse_atTop_nhds_zero_nat

lemma tendsto_nbd (f : ℕ → ℝ) (a M : ℝ) (h : Tendsto f atTop (𝓝 a)) (h' : a < M) : ∃ N, ∀ n, N ≤ n → f n < M := by
  rcases (tendsto_atTop_nhds.mp h {x | x < M} h' (isOpen_gt' M)) with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ hN n hn⟩

lemma exist_n (a M : ℝ) (k : ℕ) (h : a ^ k < M) : ∃ n : ℕ, n > 0 ∧ (a + 1 / n) ^ k < M := by
  let f := fun n : ℕ ↦ (a + 1 / n) ^ k
  rcases tendsto_nbd f (a ^ k) M (lim_add_n_inv_pow_k a k) h with ⟨n, hn⟩
  exact ⟨n + 1, ⟨by linarith, hn (n + 1) (by linarith)⟩⟩

theorem Mills_exists : Mills A := by
  have h (k : ℕ+) : Nat.Prime (Mills_seq A k) := by
    let M := Nat.floor (Mills_seq A k) + 1
    have h₀ : (Mills_seq A k) < M := by dsimp [M]; apply Nat.lt_succ_floor (Mills_seq A k)
    have h₂ : A.pnpow (pnat_cube k) < M := by
      dsimp [Mills_seq] at h₀
      apply (Nat.floor_lt (by simp)).1 h₀
    rcases exist_n A M (pnat_cube k) h₂ with ⟨N, hN₁, hN₂⟩
    have h₁ : ∃ B ∈ W, A ≤ B ∧ B < A + 1 / N := by
--      rcases Real.lt_sInf_add_pos W_real_nonempty _ with ⟨B, hB₁, hB₂⟩
      sorry
--      exact ⟨B, ⟨hB₁, A_lb B hB₁, hB₂⟩⟩
    rcases h₁ with ⟨B, hB₁, _, hB₂⟩ -- むだ？上と同様
    have h₄ : (Mills_seq A k) ≤ B.pnpow (pnat_cube k) := by sorry -- linarith [floor_le A (3 ^ k) (by linarith [Mills_gt_one]), pow_le_left A B (3 ^ k) (by linarith [Mills_gt_one]) (A_lb B hB₁)]
    have h₅ : B.pnpow (pnat_cube k) < ↑M := by sorry -- linarith [pow_lt_left B (A + 1 / N) (3 ^ k) (by norm_num) hB₁.left hB₂]
    have h₆ : Mills_seq A k = Nat.floor (B.pnpow (pnat_cube k)) := by sorry
      -- apply floor_eq A B (3 ^ k) (by linarith [hB₁.left]) ⟨h₄, _⟩
      -- simp [M] at h₅
      -- exact h₅
    rw [h₆]
    sorry
--    exact hB₁.right k hk
  exact ⟨Mills_gt_one, h⟩
