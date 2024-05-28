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
    have : A < A + 1 / N := by simp; exact hN₁
    rcases (@exists_lt_of_csInf_lt ℝ≥0 _ W (A + 1 / N) W_nonempty this) with ⟨B, hB₁, hB₂⟩
    have hAB : A ≤ B := csInf_le (by simp) hB₁
    have h₄ : (Mills_seq A k) ≤ B.pnpow (pnat_cube k) := by calc
        (Mills_seq A k) ≤ A.pnpow (pnat_cube k) := by apply Nat.floor_le; simp
        _ ≤ B.pnpow (pnat_cube k) := by apply pnpow_le (pnat_cube k) hAB
    have h₅ : B.pnpow (pnat_cube k) < ↑M := by calc
      B.pnpow (pnat_cube k) < (A + 1 / N).pnpow (pnat_cube k) := by apply pnpow_lt (pnat_cube k) hB₂
      _ < M := hN₂
    have h₆ : Nat.floor (B.pnpow (pnat_cube k)) = Mills_seq A k := by
      rw [Nat.floor_eq_iff (by simp)]
      dsimp [M] at h₅
      simp at h₅
      exact ⟨h₄, h₅⟩
    have h₇ : Nat.floor (B.pnpow (pnat_cube k)) = Mills_seq B k := rfl
    rw [← h₆, h₇]
    exact hB₁.right k
  exact ⟨Mills_gt_one, h⟩
