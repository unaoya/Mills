import Mills.Defs
import Mills.thm3

open Filter Topology NNReal

/--
$\lim_{n \to \infty} (a + \frac{1}{n})^k = a^k$
-/
lemma lim_add_n_inv_pow_k (a : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (a + 1 / n) ^ k) atTop (𝓝 (a ^ k)) := by
  apply Tendsto.comp (g := fun x => x ^ k) (y := 𝓝 a)
  · apply Continuous.tendsto
    continuity
  · apply Tendsto.comp (y := 𝓝 0) (g := fun x => a + x)
    · convert Continuous.tendsto (f := fun x => a + x) _ _
      simp
      continuity
    · exact tendsto_one_div_atTop_nhds_zero_nat

/--
任意の$a, M, k$で$a^k < M$なるものに対し、
正の整数$n$で、$(a + \frac{1}{n}) ^ k < M$となるものが存在する。
-/
lemma exist_n (a M : ℝ) (k : ℕ) (h : a ^ k < M) :
    ∃ n : ℕ, n > 0 ∧ (a + 1 / n) ^ k < M := by
  obtain ⟨n, hn⟩ := by
    apply tendsto_atTop_nhds.mp (lim_add_n_inv_pow_k a k) (Set.Iio M) h isOpen_Iio
  exact ⟨n + 1, ⟨by linarith, hn (n + 1) (by linarith)⟩⟩

theorem Mills_exists : Mills A := by
  constructor
  · exact Mills_gt_one
  · intro k
    let M := Nat.floor (Mills_seq A k).val + 1
    obtain ⟨N, hN₁, hN₂⟩ := by
      apply exist_n A M (pnat_cube k)
      apply (Nat.floor_lt (by simp)).1
      apply Nat.lt_succ_floor (Mills_seq A k).val
    obtain ⟨B, hB₁, hB₂⟩ := by
      have : A < A + 1 / N := by simp [hN₁]
      apply exists_lt_of_csInf_lt (b := (A + 1 / N)) W_nonempty this
    have : (Mills_seq B k).val = (Mills_seq A k).val := by
      apply (Nat.floor_eq_iff _).mpr
      constructor
      · calc
          (Mills_seq A k).val ≤ A ^ (pnat_cube k) := by apply Nat.floor_le; simp
          _ ≤ B ^ (pnat_cube k) := by
            apply pnpow_le
            apply csInf_le
            simp
            exact hB₁
      · calc
            B ^ (pnat_cube k) < (A + 1 / N) ^ (pnat_cube k) := by apply pnpow_lt (pnat_cube k) hB₂
            _ < M := hN₂
            _ = Mills_seq A k + 1 := by simp [M]
      simp
    rw [← this]
    exact hB₁.right k
