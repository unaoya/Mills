import Mills.Lemmas

open Filter Topology NNReal

-- ここから本題
def θ : ℝ := 0.525
noncomputable def θ' : ℝ≥0 := 0.525

-- 名前は変えたほうがいいかも。元の文章では最小のものをミルズ数と呼ぶので。
-- 自然数の範囲を変える代わりにここを変えれば大丈夫？
def Mills (x : ℝ) : Prop := 1 < x ∧ ∀ k : ℕ, 0 < k → Nat.Prime (Nat.floor (x ^ (3 ^ k)))
def Mills' (x : ℝ≥0) : Prop := 1 < x ∧ ∀ k : ℕ, 0 < k → Nat.Prime (Nat.floor (x ^ (3 ^ k)))

def Mills_lb (x : ℝ) : Mills x → 2 ^ ((1 : ℝ) / 3) ≤ x := by
  intro h
  have h₂ : 2 ≤ x ^ 3 := hfloor 2 (x ^ 3) (Nat.prime_def_lt.1 (h.right 1 (by linarith))).1 (pow_nonneg (by linarith [h.left]) 3)
  apply (cubic_le 2 x (by norm_num) (by linarith [h.left])).2 h₂


-- axiomがいいか、引用だけするけど証明はしない定理の扱い
-- xを自然数としたが問題あるか？
axiom BHP : ∃ (x₀ : ℝ), 2 ≤ x₀ ∧ ∀ (x : ℕ), x ≥ x₀ → ∃ (p : ℕ), (x ≤ p ∧ p ≤ x + ((Nat.cast : ℕ → ℝ) x) ^ θ ∧ Nat.Prime p)

noncomputable def BHP_const : ℝ := Classical.choose BHP

lemma BHP_const_ge2 : 2 ≤ BHP_const := (Classical.choose_spec BHP).left

noncomputable def BHP_const_nat : ℕ := Nat.ceil BHP_const

noncomputable def BHP_const_pnat : ℕ+ :=
  {
    val := BHP_const_nat
    property := by sorry
  }

lemma BHP_const_pnat_ge2 : 2 ≤ BHP_const_pnat := sorry

lemma BHP_const_nat_ge2 : 2 ≤ BHP_const_nat := by
  have : Nat.ceil ((Nat.cast : ℕ → ℝ) 2) ≤ Nat.ceil BHP_const := Nat.ceil_le_ceil BHP_const_ge2
  rw [Nat.ceil_natCast] at this
  exact this

lemma BHP_const_nat_BHP : ∀ x : ℕ, BHP_const_nat ≤ x → ∃ (p : ℕ), (x ≤ p ∧ p ≤ x + ((Nat.cast : ℕ → ℝ) x) ^ θ ∧ Nat.Prime p) := by
  intro x hx
  have : BHP_const ≤ x := by calc
    BHP_const ≤ BHP_const_nat := by apply Nat.le_ceil
    _ ≤ x := Nat.cast_le.2 hx
  apply (Classical.choose_spec BHP).right
  apply this
