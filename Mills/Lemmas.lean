import Mills.Prelim

open Filter Topology NNReal

lemma nat_real_le (n m : ℕ) : (n : ℝ) ≤ m ↔ n ≤ m := by simp

lemma cubic_le (x y : ℝ) (xpos : 0 ≤ x) (ypos : 0 ≤ y) : x ^ ((1 : ℝ) / 3) ≤ y ↔ x ≤ y ^ 3 := by
  rw [← Real.rpow_natCast]
  simp
  apply Real.rpow_inv_le_iff_of_pos xpos ypos (by norm_num)

lemma lt_cubic (x y : ℝ) (xpos : 0 ≤ x) (ypos : 0 ≤ y) : x < y ^ ((1 : ℝ) / 3) ↔ x ^ 3 < y := by
  rw [← Real.rpow_natCast]
  simp
  apply Real.lt_rpow_inv_iff_of_pos xpos ypos (by norm_num)

lemma pow_le (x : ℝ) (n m : ℕ) (hx : 1 ≤ x) (hnm : n ≤ m) : x ^ n ≤ x ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hx (by norm_num [hnm])

lemma pow_lt (x y : ℝ) (n : ℕ) (hx : 1 < x) (hnm : y < n) : x ^ y < x ^ n := by
  rw [← Real.rpow_natCast]
  apply Real.rpow_lt_rpow_of_exponent_lt hx (by norm_num [hnm])

lemma pow_le_left (x y : ℝ) (n : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) : x ^ n ≤ y ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow (by linarith) hxy (by norm_num)

lemma pow_lt_left (x y : ℝ) (n : ℕ) (npos: 0 < n) (hx : 1 < x) (hxy : x < y) : x ^ n < y ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  apply Real.rpow_lt_rpow (by linarith) hxy (by norm_num [npos])

lemma floor_le (x : ℝ) (n : ℕ) (hx : 0 ≤ x) : Nat.floor (x ^ n) ≤ x ^ n := by
  apply Nat.floor_le
  rw [← Real.rpow_natCast]
  apply Real.rpow_nonneg (by linarith) n

lemma floor_rpow_le (x : ℝ) (y : ℝ) (hx : 0 ≤ x) : (Nat.cast : ℕ → ℝ) (Nat.floor (x ^ y)) ≤ x ^ y := by
  apply Nat.floor_le
  apply Real.rpow_nonneg (by linarith) y

-- 冪乗と型の変換を整理しておく
lemma h₃ (n k : ℕ) : (n : ℝ) ^ k = (n ^ k : ℝ) := by ring

lemma Natcast_inj (m n : ℕ) : (Nat.cast : ℕ → ℝ) n = (Nat.cast : ℕ → ℝ) m ↔ n = m := by simp

lemma cast_nat_pow_eq_rpow_cast (n m : ℕ) : (Nat.cast : ℕ → ℝ) (Nat.pow n m) = ((Nat.cast : ℕ → ℝ) n) ^ ((Nat.cast : ℕ → ℝ) m) := by simp --抽象化

-- floor周りの計算も整理しておく

lemma hfloor (n : ℕ) (x : ℝ) (h : n ≤ Nat.floor x) (xpos : 0 ≤ x) : n ≤ x := by calc
  (n : ℝ) ≤ Nat.floor x := by apply (nat_real_le n _).2 h
  _ ≤ x := by apply Nat.floor_le xpos

lemma floor_eq (x y : ℝ) (n : ℕ) (ypos : 0 < y) (h : Nat.floor (x ^ n) ≤ y ^ n ∧ y ^ n < Nat.floor (x ^ n) + 1) : Nat.floor (x ^ n) = Nat.floor (y ^ n) := by
    have h' : 0 ≤ y ^ n := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_nonneg (by linarith [le_of_lt ypos])
    have : Nat.floor (y ^ n) = Nat.floor (x ^ n) := by
      rw [Nat.floor_eq_iff h']
      exact h
    exact this.symm

-- 単調で有界な実数列は上限または下限に収束する

lemma monotone_converges_of_bdd_above (f : ℕ → ℝ) (h₁ : Monotone f) (h₂ : BddAbove (Set.range f)) :
  ∃ A, IsLUB (Set.range f) A ∧ Filter.Tendsto f atTop (𝓝 A) :=
  ⟨sSup (Set.range f), ⟨Real.isLUB_sSup ⟨f 1, by simp⟩ h₂, tendsto_atTop_isLUB h₁ (Real.isLUB_sSup ⟨f 1, by simp⟩ h₂)⟩⟩

lemma antitone_converges_of_bdd_below (f : ℕ → ℝ) (h₁ : Antitone f) (h₂ : BddBelow (Set.range f)) :
  ∃ A, IsGLB (Set.range f) A ∧ Filter.Tendsto f atTop (𝓝 A) :=
  ⟨sInf (Set.range f), ⟨Real.isGLB_sInf ⟨f 1, by simp⟩ h₂, tendsto_atTop_isGLB h₁ (Real.isGLB_sInf ⟨f 1, by simp⟩ h₂)⟩⟩
