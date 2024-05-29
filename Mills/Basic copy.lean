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

-- 自然数を1以上としたほうがいい？
-- Wの定義でnを1以上としとけば問題なさそう。
-- 命題5は自然数に0を入れても成立する。
-- 問題はp0が素数にならないことだけ？

-- 冪乗関係の話を使うときにいちいち正の数とか証明するのが面倒なので、一括で事前に書いておきたい。
-- 使うのは3^nとかp n^kとかの形くらいに限られるはず？

-- 実数乗と自然数乗の話を合わせるのが面倒なので、そこも最初にかっちりしておきたい。

-- NNRealを使うと楽？

-- 自然数を1以上に書き直す。ℕ+を使う。

-- 補助的な不等式を整理しておく
lemma nat_real_le (n m : ℕ) : (n : ℝ) ≤ m ↔ n ≤ m := by simp

-- 冪乗の不等式関係を整理しておく（名付けはライブラリを参考にしたい）
lemma cubic_le (x y : ℝ) (xpos : 0 ≤ x) (ypos : 0 ≤ y) : x ^ ((1 : ℝ) / 3) ≤ y ↔ x ≤ y ^ 3 := by
  rw [← Real.rpow_natCast]
  simp
  apply Real.rpow_inv_le_iff_of_pos xpos ypos (by norm_num)

lemma cubic_le' (x y : ℝ≥0) : x ^ ((1 : ℝ) / 3) ≤ y ↔ x ≤ y ^ 3 := by
  rw [← NNReal.rpow_natCast]
  apply NNReal.rpow_one_div_le_iff (by norm_num)

lemma cubic_lt (x y : ℝ) (xpos : 0 ≤ x) (ypos : 0 ≤ y) : x ^ ((1 : ℝ) / 3) < y ↔ x < y ^ 3 := by
  rw [← Real.rpow_natCast]
  simp
  apply Real.rpow_inv_lt_iff_of_pos xpos ypos (by norm_num)

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
-- ライブラリにありそう。

lemma monotone_converges_of_bdd_above_to_sup (f : ℕ → ℝ) (h₁ : Monotone f) (h₂ : BddAbove (Set.range f)) :
  Filter.Tendsto f atTop (𝓝 (sSup (Set.range f))) := tendsto_atTop_isLUB h₁ (Real.isLUB_sSup (Set.range f) ⟨f 1, by simp⟩ h₂)

lemma monotone_converges_of_bdd_above (f : ℕ → ℝ) (h₁ : Monotone f) (h₂ : BddAbove (Set.range f)) :
  ∃ A, IsLUB (Set.range f) A ∧ Filter.Tendsto f atTop (𝓝 A) :=
  ⟨sSup (Set.range f), ⟨Real.isLUB_sSup (Set.range f) ⟨f 1, by simp⟩ h₂, tendsto_atTop_isLUB h₁ (Real.isLUB_sSup (Set.range f) ⟨f 1, by simp⟩ h₂)⟩⟩

lemma antitone_converges_of_bdd_below_to_inf (f : ℕ → ℝ) (h₁ : Antitone f) (h₂ : BddBelow (Set.range f)) :
  Filter.Tendsto f atTop (𝓝 (sInf (Set.range f))) := tendsto_atTop_isGLB h₁ (Real.is_glb_sInf (Set.range f) ⟨f 1, by simp⟩ h₂)

lemma antitone_converges_of_bdd_below (f : ℕ → ℝ) (h₁ : Antitone f) (h₂ : BddBelow (Set.range f)) :
  ∃ A, IsGLB (Set.range f) A ∧ Filter.Tendsto f atTop (𝓝 A) :=
  ⟨sInf (Set.range f), ⟨Real.is_glb_sInf (Set.range f) ⟨f 1, by simp⟩ h₂, tendsto_atTop_isGLB h₁ (Real.is_glb_sInf (Set.range f) ⟨f 1, by simp⟩ h₂)⟩⟩

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

lemma BHP_const_nat_ge2 : 2 ≤ BHP_const_nat := by
  have : Nat.ceil ((Nat.cast : ℕ → ℝ) 2) ≤ Nat.ceil BHP_const := Nat.ceil_le_ceil 2 BHP_const BHP_const_ge2
  rw [Nat.ceil_natCast] at this
  exact this

lemma BHP_const_nat_BHP : ∀ x : ℕ, BHP_const_nat ≤ x → ∃ (p : ℕ), (x ≤ p ∧ p ≤ x + ((Nat.cast : ℕ → ℝ) x) ^ θ ∧ Nat.Prime p) := by
  intro x hx
  have : BHP_const ≤ x := by calc
    BHP_const ≤ BHP_const_nat := by apply Nat.le_ceil
    _ ≤ x := Nat.cast_le.2 hx
  apply (Classical.choose_spec BHP).right
  apply this

-- def Step : ℕ → ℕ → Prop := fun p q => p ^ 3 ≤ q ∧ q < (p + 1) ^ 3 - 1 ∧ Nat.Prime q

def Step' : ℕ → ℕ → Prop := fun p q => p ^ 3 ≤ q ∧ (Nat.cast : ℕ → ℝ) q ≤ (Nat.cast : ℕ → ℝ) p ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) p ^ (((Nat.cast : ℕ → ℝ) 3) * θ) ∧ q < (p + 1) ^ 3 - 1 ∧ Nat.Prime q

lemma Step_aux (n m : ℕ) (h : n ^ 3 ≤ m) (h' : BHP_const_nat ≤ n) : BHP_const_nat ≤ m := by
  have : 3 ≠ 0 := by linarith [BHP_const_nat_ge2]
  linarith [Nat.le_self_pow this n]

--これは一般的な補題なので外に切り出す、後でも再証明してる？
lemma aux : ∀ x : ℝ, BHP_const ≤ x → x ^ (Nat.cast : (ℕ → ℝ)) 3 + x ^ ((Nat.cast : ℕ → ℝ) 3 * θ) < (x + 1) ^ (Nat.cast : ℕ → ℝ) 3 - 1 := by
  intro x hx
  have : (Nat.cast : (ℕ → ℝ)) 3 * θ < (Nat.cast : (ℕ → ℝ)) 2 := by rw [θ]; norm_num;
  calc
    x ^ (Nat.cast : (ℕ → ℝ)) 3 + x ^ ((Nat.cast : (ℕ → ℝ)) 3 * θ) < x ^ (Nat.cast : (ℕ → ℝ)) 3 + x ^ (Nat.cast : (ℕ → ℝ)) 2 := add_lt_add_left (Real.rpow_lt_rpow_of_exponent_lt (by linarith [BHP_const_ge2]) this) (x ^ (Nat.cast : (ℕ → ℝ)) 3)
    _ ≤ x ^ (Nat.cast : (ℕ → ℝ)) 3 + 3 * x ^ (Nat.cast : (ℕ → ℝ)) 2 := by
      have : 0 ≤ x ^ (Nat.cast : (ℕ → ℝ)) 2 := Real.rpow_nonneg (by linarith [BHP_const_ge2]) ((Nat.cast : ℕ → ℝ) 2)
      linarith
    _ ≤ x ^ (Nat.cast : (ℕ → ℝ)) 3 + 3 * x ^ (Nat.cast : (ℕ → ℝ)) 2 + 3 * x := by linarith [BHP_const_ge2]
    _ = (x + 1) ^ (Nat.cast : (ℕ → ℝ)) 3 - 1 := by rw [Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]; ring_nf

lemma Stepex : ∀ p : ℕ, BHP_const_nat ≤ p → ∃ (q : ℕ), Step' p q := by
  intro p hp
  have hp' : BHP_const ≤ p := by calc
    BHP_const ≤ BHP_const_nat := by apply Nat.le_ceil
    _ ≤ p := by rw [Nat.cast_le]; exact hp
  have : BHP_const_nat ≤ p ^ 3 := by calc
    BHP_const_nat ≤ p := hp
    _ ≤ p ^ 3 := by apply Nat.le_self_pow (by linarith)
  rcases BHP_const_nat_BHP (p ^ 3) this with ⟨q, hq₁, hq₂, hq₃⟩
  use q
  have hq₅ : (Nat.cast : ℕ → ℝ) q ≤ (Nat.cast : ℕ → ℝ) p ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) p ^ (((Nat.cast : ℕ → ℝ) 3) * θ) := by
    have : (Nat.cast : ℕ → ℝ) (p ^ 3) = (Nat.cast : ℕ → ℝ) p ^ (Nat.cast : ℕ → ℝ) 3 := by simp [← Real.rpow_natCast]
    rw [this, ← Real.rpow_mul (by linarith [BHP_const_ge2])] at hq₂
    exact hq₂
  have hq₄ : q < (p + 1) ^ 3 - 1 := by
    have : (Nat.cast : (ℕ → ℝ)) q < (Nat.cast : (ℕ → ℝ)) ((p + 1) ^ 3 - 1) := by calc
      (Nat.cast : (ℕ → ℝ)) q ≤ (Nat.cast : ℕ → ℝ) p ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) p ^ (((Nat.cast : ℕ → ℝ) 3) * θ) := hq₅
      _ <  (((Nat.cast : (ℕ → ℝ)) p + 1) ^ (Nat.cast : (ℕ → ℝ)) 3 - 1) := aux p hp'
      _ = (Nat.cast : (ℕ → ℝ)) ((p + 1) ^ 3 - 1) := by simp; rw [← Real.rpow_natCast]; ring_nf
    exact Nat.cast_lt.1 this
  exact ⟨hq₁, hq₅, hq₄, hq₃⟩

noncomputable instance (m : ℕ) : DecidablePred (Step' m) := fun _ ↦ And.decidable

def NgeBHP : Type := {n : ℕ // BHP_const_nat ≤ n}

-- defじゃなくてletとかで証明の内部でやりたいけど、できる？
-- これはAを使って作ったやつじゃなくて、適当な初期値から作ったやつ。
noncomputable def pp' : ℕ → NgeBHP
| 0 => ⟨BHP_const_nat, le_refl BHP_const_nat⟩
| (n + 1) => ⟨Nat.find (Stepex (pp' n).val (pp' n).property), Step_aux (pp' n).val (Nat.find (Stepex (pp' n).val (pp' n).property)) (Nat.find_spec (Stepex (pp' n).val (pp' n).property)).left (pp' n).property⟩

noncomputable def pp : ℕ → ℕ := fun n ↦ (pp' n).val

lemma hpp' : ∀ k : ℕ, Step' (pp k) (pp (k + 1)) := by intro k; exact Nat.find_spec (Stepex (pp' k).val (pp' k).property)

lemma hpp : ∀ k : ℕ, (pp k) ^ 3 ≤ pp (k + 1) ∧ (Nat.cast : ℕ → ℝ) (pp (k + 1)) ≤ (Nat.cast : ℕ → ℝ) (pp k) ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) (pp k) ^ (((Nat.cast : ℕ → ℝ) 3) * θ) ∧ pp (k + 1) < ((pp k) + 1) ^ 3 - 1 ∧ Nat.Prime (pp (k + 1)) := fun k ↦ hpp' k

lemma pnonneg (n : ℕ) : 0 ≤ pp n := by linarith [(Nat.prime_def_lt.1 (hpp n).2.2.2).1]

lemma rpnonneg (n : ℕ) : 0 ≤ (Nat.cast : ℕ → ℝ) (pp n) := by apply Nat.cast_nonneg

/-
lemma A_pow_nonneg (n : ℕ) : 0 ≤ A ^ n := by rw [← Real.rpow_natCast]; apply Real.rpow_nonneg (by linarith [Mills_gt_one])

lemma A_rpow_nonneg (x : ℝ) : 0 ≤ A ^ x := by apply Real.rpow_nonneg (by linarith [Mills_gt_one])

lemma A_pow_gt_one (n : ℕ) (npos : 0 < n) : 1 < A ^ n := by
  rw [← Real.rpow_natCast]
  calc
    1 = 1 ^ (n : ℝ) := by simp
    _ < A ^ (n : ℝ) := Real.rpow_lt_rpow (by linarith) (Mills_gt_one) (by simp [npos])
-- infがちゃんと最小になることを証明し、本来の意味でのミルズ数が存在することを示す
-- 準備として収束に関する命題を示す。
section

variable (a : ℝ) (k : ℕ)

def f : ℝ → ℝ := (fun x : ℝ ↦ x ^ k) ∘ (fun x : ℝ ↦ a + x)

lemma h'' (a : ℝ) (k : ℕ) : Tendsto (fun n : ℕ ↦ (a + 1 / n) ^ k) atTop (𝓝 (a ^ k)) := by
  have : (fun n : ℕ ↦ (a + 1 / n ) ^ k) = f a k ∘ (fun n : ℕ ↦ (n : ℝ)⁻¹) := by funext; rw [f]; simp
  rw [this]
  have : Tendsto (f a k) (𝓝 0) (𝓝 (f a k 0)) := Continuous.tendsto (Continuous.comp (continuous_pow k) (continuous_add_left a)) 0
  simp [f] at this
  apply tendsto_nhds_iff_seq_tendsto.mp this
  exact tendsto_inverse_atTop_nhds_zero_nat

lemma h''' (f : ℕ → ℝ) (a M : ℝ) (h : Tendsto f atTop (𝓝 a)) (h' : a < M) : ∃ N, ∀ n, N ≤ n → f n < M := by
  rcases (tendsto_atTop_nhds.mp h {x | x < M} h' (isOpen_gt' M)) with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ hN n hn⟩

lemma exist_n (a M : ℝ) (k : ℕ) (h : a ^ k < M) : ∃ n : ℕ, n > 0 ∧ (a + 1 / n) ^ k < M := by
  let f := fun n : ℕ ↦ (a + 1 / n) ^ k
  rcases h''' f (a ^ k) M (h'' a k) h with ⟨n, hn⟩
  exact ⟨n + 1, ⟨by linarith, hn (n + 1) (by linarith)⟩⟩
end


noncomputable def p : ℕ → ℕ := fun n ↦ Nat.floor (A ^ (3 ^ n))

noncomputable def p' : ℕ → ℝ := fun n ↦ (Nat.cast : ℕ → ℝ) (p n)

noncomputable def p''' : ℕ → ℝ := fun n ↦ (Nat.floor (A ^ ((3 : ℝ) ^ (n : ℝ))) : ℝ)

lemma p'eqp''' (n : ℕ) : p' n = p''' n := by
  rw [p', p''', p]
  simp
  apply congrArg
  rw [← Real.rpow_natCast]
  simp

lemma pn_ge_2 (n : ℕ) (h : 0 < n) : 2 ≤ p n := by apply Nat.Prime.two_le (Mills_exists.right n h)

lemma Apow_ge_2 (n : ℕ) (h : 0 < n) : 2 ≤ A ^ 3 ^ n := by calc
  (Nat.cast : ℕ → ℝ) 2 ≤ (Nat.cast : ℕ → ℝ) (p n) := Nat.cast_le.2 (pn_ge_2 n h)
  _ = Nat.floor (A ^ 3 ^ n) := by rw [p]
  _ ≤ A ^ 3 ^ n := Nat.floor_le (A_pow_nonneg (3 ^ n))

lemma floor_lt_diff_1 (x y : ℝ) (xpos : 0 ≤ x) (h : x + 1 < y) : Nat.floor x < Nat.floor y := by
  have h₀ : Nat.floor (x + 1) = Nat.floor x + 1 := by apply Nat.floor_add_one xpos
  have h₁ : Nat.floor (x + 1) ≤ Nat.floor y := by apply Nat.floor_le_floor; linarith
  rw [h₀] at h₁
  linarith

-- lemma Mills_gt_one : 1 < A := by
lemma pk_str_mono : ∀ n, p (n + 1) < p (n + 2) := by
  intro n
  rw [p, p]
  have : A ^ 3 ^ (n + 1) + 1 < A ^ 3 ^ (n + 2) := by calc -- 似てる計算をどっかでやってる。抽象化できる？
    A ^ 3 ^ (n + 1) + 1 < A ^ 3 ^ (n + 1) + A ^ 3 ^ (n + 1) := by linarith [A_pow_gt_one (3 ^ (n + 1)) (by norm_num)]
    _ = A ^ 3 ^ (n + 1) * 2 := by ring
    _ ≤ A ^ 3 ^ (n + 1) * A ^ 3 ^ (n + 1) := by apply (mul_le_mul_left (by linarith [A_pow_gt_one (3 ^ (n + 1)) (by norm_num)])).2 (Apow_ge_2 (n + 1) (by norm_num))
    _ = A ^ 3 ^ (n + 1) * A ^ 3 ^ (n + 1) * 1 := by ring
    _ ≤ A ^ 3 ^ (n + 1) * A ^ 3 ^ (n + 1) * A ^ 3 ^ (n + 1) := by
      apply (mul_le_mul_left _).2 (by linarith [Apow_ge_2 (n + 1) (by norm_num)])
      apply mul_pos <;> linarith [A_pow_gt_one (3 ^ (n + 1)) (by norm_num)]
    _ = A ^ 3 ^ (n + 2) := by group
  exact floor_lt_diff_1 (A ^ 3 ^ (n + 1)) (A ^ 3 ^ (n + 2)) (A_pow_nonneg (3 ^ (n + 1))) this

lemma pk_ge_k (k : ℕ) : k + 1 ≤ p (k + 1) := by
  induction' k with k hk
  case zero => linarith [pn_ge_2 1 (by norm_num)]
  case succ => linarith [pk_str_mono k]

lemma prime_seq' (n : ℕ) : 0 < n → Nat.Prime (p n) := by rw [p]; apply Mills_exists.right n

lemma pgt1 (n : ℕ) : 0 < n → p n > 1 := by exact fun h ↦ (Nat.prime_def_lt.1 (prime_seq' n h)).1

lemma pgt1' (n : ℕ) : 0 < n → p' n > 1 := by rw [p']; simp; exact pgt1 n

lemma p'pos (n : ℕ) : 0 < n → 0 < p' n := by intro h; linarith [pgt1' n h]

lemma ppos (n : ℕ) : 0 < n → 0 < p n := by intro h; linarith [pgt1 n h]


-- qを0から作っておいて、定理の中で平行移動する？q' n = q (k + n)みたいな。
noncomputable def qq' : NgeBHP → ℕ → NgeBHP :=
fun m ↦
  fun n ↦
    match n with
      | 0 => m
      | (n + 1) => ⟨Nat.find (Stepex (qq' m n).val (qq' m n).property), Step_aux (qq' m n).val (Nat.find (Stepex (qq' m n).val (qq' m n).property)) (Nat.find_spec (Stepex (qq' m n).val (qq' m n).property)).left (qq' m n).property⟩

noncomputable def qq (m : NgeBHP) : ℕ → ℕ := fun n ↦ (qq' m n).val

lemma hqq' (m : NgeBHP) : ∀ k : ℕ, Step' (qq m k) (qq m (k + 1)) := by
  intro k
  exact Nat.find_spec (Stepex (qq' m k).val (qq' m k).property)

lemma hqq (m : NgeBHP) : ∀ k : ℕ, (qq m k) ^ 3 ≤ qq m (k + 1) ∧ (Nat.cast : ℕ → ℝ) (qq m (k + 1)) ≤ (Nat.cast : ℕ → ℝ) (qq m k) ^ (Nat.cast : ℕ → ℝ) 3 + (Nat.cast : ℕ → ℝ) (qq m k) ^ (((Nat.cast : ℕ → ℝ) 3) * θ) ∧ qq m (k + 1) < ((qq m k) + 1) ^ 3 - 1 ∧ Nat.Prime (qq m (k + 1)) := fun k ↦ hqq' m k

lemma qnonneg (m : NgeBHP) (n : ℕ) : 0 ≤ qq m n := by simp

lemma qpnonneg (m : NgeBHP) (n : ℕ) : 0 ≤ (Nat.cast : ℕ → ℝ) (qq m n) := by simp

lemma qq_gt_1 : ∀ m, 1 < qq (m : NgeBHP) 1 := by
  intro m
  rw [qq]
  linarith [(qq' m 1).property, BHP_const_nat_ge2]

lemma prop5 : ∃ k₀, ∀ k, k₀ ≤ k → p' k ^ ((Nat.cast : ℕ → ℝ) 3) ≤ p' (k + 1) ∧ p' (k + 1) ≤ (p' k) ^ ((Nat.cast : ℕ → ℝ) 3) + (p' k) ^ (3 * θ) := by
  by_contra h
  push_neg at h
  rcases h BHP_const_nat with ⟨k, h₀, h₁⟩
  have : 0 < k := by linarith [BHP_const_nat_ge2]
  have : k.pred.succ = k := by apply Nat.succ_pred_eq_of_pos this
  have : k ≤ p k := by rw [← this]; apply pk_ge_k k.pred
  have h' : BHP_const_nat ≤ p k := by linarith [this]
  let q : ℕ → ℕ := fun n ↦ if n ≤ k then p n else qq ⟨p k, h'⟩ (n - k)
  let q₀ : ℕ → ℕ
  | 0 => 1
  | (n + 1) => if n + 1 ≤ k then p (n + 1) else qq ⟨p k, h'⟩ ((n + 1) - k)
  have q₀_eq_q (n : ℕ) (npos : 0 < n) : q₀ n = q n := by
    cases n
    case zero => linarith
    case succ => dsimp [q, q₀]
  have h_q_le_k (n : ℕ) (npos : 0 < n) : n ≤ k → q n = p n := by
    intro hn
    dsimp [q]
    split_ifs
    rfl
  have h_q_gt_k : ∀ n, k < n → q n = qq ⟨p k, h'⟩ (n - k) := by
    intro n hn
    dsimp [q]
    split_ifs
    · linarith
    · rfl
  let C' : ℝ := left_lim q
  have h_q_left : (n : ℕ) → q n ^ 3 ≤ q (n + 1) := by
    intro n
    induction' n with n hn
    case zero =>
      have qp0 : q 0 = p 0 := by dsimp [q]; split_ifs; rfl; linarith
      have qp1 : q 1 = p 1 := by dsimp [q]; split_ifs; rfl; linarith
      rw [qp0, qp1]
      dsimp [p]
      simp
      have hA₀ : (Nat.cast : ℕ → ℝ) (Nat.floor A) ^ (Nat.cast : ℕ → ℝ) 3 ≤ A ^ (Nat.cast : ℕ → ℝ) 3 := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by linarith [Mills_gt_one])
        apply Nat.floor_le (by linarith [Mills_gt_one])
      have hA₁ : Nat.floor ((Nat.cast : ℕ → ℝ) (Nat.floor A) ^ (Nat.cast : ℕ → ℝ) 3) ≤ Nat.floor (A ^ (Nat.cast : ℕ → ℝ) 3) := by
        apply Nat.floor_le_floor
        exact hA₀
      have hA₂ : Nat.floor ((Nat.cast : ℕ → ℝ) (Nat.floor A) ^ (Nat.cast : ℕ → ℝ) 3) = (Nat.floor A) ^ 3 := by
        rw [← cast_nat_pow_eq_rpow_cast]
        rw [Nat.floor_coe]
        simp
      rw [hA₂] at hA₁
      rw [Real.rpow_natCast] at hA₁
      exact hA₁
    case succ =>
    dsimp [q]
    split_ifs
    · have : (p' n.succ) ^ ((Nat.cast : ℕ → ℝ) 3) ≤ p' (n.succ + 1) := by
        apply (lem6 n.succ _).left
        linarith
      dsimp only [p'] at this
      rw [← cast_nat_pow_eq_rpow_cast] at this
      apply Nat.cast_le.1 this
    · have : n.succ = k := by linarith
      rw [this]
      simp
      exact (hqq' ⟨p k, h'⟩ 0).left
    · linarith
    · rw [Nat.sub_add_comm]
      exact (hqq' ⟨p k, h'⟩ (n.succ - k)).left
      linarith
  have h_q_right : (n : ℕ) → q (n + 1) < ((q n) + 1) ^ 3 - 1 := by
    intro n
    induction' n with n hn
    case zero =>
      dsimp [q₀]
      simp
      have qp0 : q 0 = p 0 := by dsimp [q]; split_ifs; rfl; linarith
      have qp1 : q 1 = p 1 := by dsimp [q]; split_ifs; rfl; linarith
      rw [qp0, qp1]
      dsimp [p]
      simp
      have : Int.floor (A ^ 3) < (Int.floor A + 1) ^ 3 - 1 := by
        have : Int.floor A + Int.fract A = A := by apply Int.floor_add_fract
        rw [← this]
        ring_nf
        simp
        sorry
      sorry
    case succ =>
    dsimp [q]
    split_ifs
    · have hp₁ : p' (n.succ + 1) < (p' n.succ + 1) ^ ((Nat.cast : ℕ → ℝ) 3) - 1 := by
        apply (lem6 n.succ (by linarith)).right
      have hp₂ : (p' n.succ + 1) ^ ((Nat.cast : ℕ → ℝ) 3) - 1 = (Nat.cast : ℕ → ℝ) ((p n.succ + 1) ^ 3 - 1) := by
        rw [p']
        simp
        rw [← Real.rpow_natCast]
        simp
      rw [hp₂] at hp₁
      dsimp only [p'] at hp₁
      apply Nat.cast_lt.1 hp₁
    · have nsucc_eq_k : n.succ = k := by linarith
      rw [nsucc_eq_k]
      simp
      dsimp [qq, qq']
      have hp₁ : p' (n.succ + 1) < (p' n.succ + 1) ^ ((Nat.cast : ℕ → ℝ) 3) - 1 := by
        apply (lem6 n.succ (by linarith)).right
      have hp₂ : (p' n.succ + 1) ^ ((Nat.cast : ℕ → ℝ) 3) - 1 = (Nat.cast : ℕ → ℝ) ((p n.succ + 1) ^ 3 - 1) := by
        rw [p']
        simp
        rw [← Real.rpow_natCast]
        simp
      rw [hp₂] at hp₁
      dsimp only [p'] at hp₁
      rw [nsucc_eq_k] at hp₁
      apply Nat.cast_lt.1 hp₁
    · have : n.succ = k := by linarith
      rw [this]
      simp
      rw [qq]
      exact (hqq' ⟨p k, h'⟩ 0).right.right.left
    · rw [Nat.sub_add_comm]
      exact (hqq' ⟨p k, h'⟩ (n.succ - k)).right.right.left
      linarith
  have q1_gt_1 : 1 < q 1 := by rw [h_q_le_k 1 (by linarith) (by linarith)]; apply pgt1 1; norm_num
  have mono_left_q : Monotone (seq_left q) := by exact mono_left q h_q_left
  have C'_floor (n : ℕ) : Nat.floor (C' ^ 3 ^ n) = q n := by
    apply left_floor_eq_seq q h_q_left h_q_right n
  have C'_gt_1 : 1 < C' := left_lim_gt_1 q h_q_right q1_gt_1
  have Prime_q (n : ℕ) (npos : 0 < n) : Nat.Prime (q n) := by
    dsimp [q]
    split_ifs
    · exact prime_seq' n npos
    · have : k < n := by linarith
      have : 0 < n - k := by apply Nat.pos_of_ne_zero; intro h; linarith [Nat.le_of_sub_eq_zero h]
      have : (n - k).pred.succ = n - k := by rw [Nat.succ_pred_eq_of_pos this]
      rw [← this]
      exact (hqq' ⟨p k, h'⟩ ((n - k).pred)).right.right.right  --数合わせ
  have C'inW : C' ∈ W := by
    constructor
    · exact C'_gt_1
    · intro n hn
      rw [left_floor_eq_seq q h_q_left h_q_right n, ← Nat.succ_pred_eq_of_pos hn]
      exact Prime_q n.pred.succ (by linarith)
  have C'ltA : C' < A := by
    have hh₀ : Nat.floor (C' ^ 3 ^ (k + 1)) = q (k + 1) := by apply C'_floor
    have hh₁ : q (k + 1) < p (k + 1) := by
      have : (Nat.cast : ℕ → ℝ) (q (k + 1)) < (Nat.cast : ℕ → ℝ) (p (k + 1)) := by calc
        (Nat.cast : ℕ → ℝ) (q (k + 1)) ≤ (p k) ^ (Nat.cast : ℕ → ℝ) 3 + (p k) ^ (3 * θ) := by
          dsimp [q]
          split_ifs
          · linarith
          · have : k + 1 - k = 1 := by
              rw [Nat.sub_add_comm]
              simp
              linarith
            rw [this]
            exact (hqq ⟨p k, h'⟩ 0).right.left
        _ < (Nat.cast : ℕ → ℝ) (p (k + 1)) := by apply h₁ (lem6 k (by linarith [h₀, BHP_const_nat_ge2])).left
      apply Nat.cast_lt.1 this
    have hh₂ : q (k + 1) + 1 ≤ p (k + 1) := Nat.succ_le.2 hh₁
    have hh₃ : C' ^ 3 ^ (k + 1) < p (k + 1) := by
      calc
        C' ^ 3 ^ (k + 1) < q (k + 1) + 1 := by
          apply ((Nat.floor_eq_iff _).1 hh₀).right
          rw [← Real.rpow_natCast]
          apply Real.rpow_nonneg (by linarith [C'inW.left])
        _ = (Nat.cast : ℕ → ℝ) (q (k + 1) + 1) := by simp
        _ ≤ p (k + 1) := by rw [Nat.cast_le]; exact hh₂
    have hh₄ : p (k + 1) = Nat.floor (A ^ 3 ^ (k + 1)) := by rw [p]
    have hh₅ : C' ^ 3 ^ (k + 1) < A ^ 3 ^ (k + 1) := by -- hh₃からhh₅を一つにまとめる。
      calc
        C' ^ 3 ^ (k + 1) < p (k + 1) := hh₃
        _ = Nat.floor (A ^ 3 ^ (k + 1)) := by apply congrArg; exact hh₄
        _ ≤ A ^ 3 ^ (k + 1) := by apply Nat.floor_le; apply A_pow_nonneg
    have : 0 < (Nat.cast : ℕ → ℝ) (3 ^ (k + 1)) := by norm_num
    rw [← Real.rpow_lt_rpow_iff (by linarith [C'inW.left]) (by linarith [Mills_gt_one]) this]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast] at hh₅
    exact hh₅
  have : A ≤ C' := A_lb C' C'inW
  linarith

lemma prop5' : ∃ k₀ > 1, ∀ k, k₀ ≤ k → p' k ^ (3 : ℝ) ≤ p' (k + 1) ∧ p' (k + 1) ≤ (p' k) ^ (3 : ℝ) + (p' k) ^ (3 * θ) := by
  rcases prop5 with ⟨k₀, h⟩
  exact ⟨k₀ + 2, ⟨(by norm_num), fun k hk ↦ h k (by linarith)⟩⟩

--似たようなことをやってる
lemma lem7'''' (k : ℕ) : (p' 1) ^ (((Nat.cast : ℕ → ℝ) 3) ^ k) ≤ p' (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      p' 1 ^ ((Nat.cast : ℕ → ℝ) 3) ^ (Nat.succ k) = (p' 1 ^ ((Nat.cast : ℕ → ℝ) 3) ^ (k + 1)) := by simp
      _ = (p' 1 ^ (((Nat.cast : ℕ → ℝ) 3) ^ k * ((Nat.cast : ℕ → ℝ) 3) ^ 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, Nat.cast_add, Real.rpow_add]; simp
      _ = (p' 1 ^ (((Nat.cast : ℕ → ℝ) 3) ^ k * ((Nat.cast : ℕ → ℝ) 3))) := by simp
      _ = (p' 1 ^ ((Nat.cast : ℕ → ℝ) 3) ^ k) ^ ((Nat.cast : ℕ → ℝ) 3) := by rw [Real.rpow_mul]; apply le_of_lt (p'pos 1 (by norm_num))
      _ ≤ (p' (k + 1)) ^ ((Nat.cast : ℕ → ℝ) 3) := by
        rw [Real.rpow_natCast _ 3, Real.rpow_natCast _ 3]
        apply pow_le_left
        apply Real.one_le_rpow _ (by norm_num)
        apply le_of_lt (pgt1' 1 (by norm_num))
        exact ih
      _ ≤ p' (k + 2) := (lem6 (k + 1) (by norm_num)).left
      _ = p' (Nat.succ k + 1) := by simp

lemma floor_lt_succ (x y : ℝ) (h : Nat.floor x ≤ y) : x ≤ y + 1 := by
  calc
    x ≤ Nat.ceil x := Nat.le_ceil x
    _ ≤ Nat.floor x + (Nat.cast : ℕ → ℝ) 1 := by rw [← Nat.cast_add, Nat.cast_le]; apply Nat.ceil_le_floor_add_one x
    _ = Nat.floor x + 1 := by simp
    _ ≤ y + 1 := by linarith

lemma lem7 : ∃ γ > 0, ∃ k₁ > 1, ∀ k, k₁ ≤ k → |A ^ ((3 : ℝ) ^ k) - p' k| ≤ Real.exp (-γ * ((3 : ℝ) ^ k)) := by
  rcases prop5' with ⟨k₀, h, h'⟩
  use (2 - 3 * θ) / 3 * Real.log (p 1)
  constructor
  · exact Right.mul_pos (by rw [θ]; norm_num) (Real.log_pos (pgt1' 1 (by norm_num)))
  · use k₀
    constructor
    · exact h
    · intro k hk
      have h₃ : p' k ≤ A ^ ((3 : ℝ) ^ k) := by
        rw [p'eqp''', p''', ← Real.rpow_natCast]
        apply floor_rpow_le _ _ (by linarith [Mills_gt_one])
      have h₄ : A ^ ((3 : ℝ) ^ k) ≤ p' k * (1 + 2 * (p' k) ^ (3 * (θ - 1))) ^ ((1 : ℝ) / 3) := by
        have hh₀ : p' (k + 1) ≤ p' k ^ (3 : ℝ) + p' k ^ (3 * θ) := (h' k hk).right
        have hh₂ : A ^ (3 : ℝ) ^ (k + 1) ≤ p' k ^ (3 : ℝ) + p' k ^ (3 * θ) + 1 := by
          rw [p'eqp''', p'''] at hh₀
          rw [← Real.rpow_natCast]
          apply floor_lt_succ
          exact hh₀
        have hh₃ : p' k ^ (3 : ℝ) + p' k ^ (3 * θ) + 1 ≤ p' k ^ (3 : ℝ) * (1 + 2 * (p' k) ^ (3 * (θ - 1))) := lem7''''' (p' k) (by linarith [pgt1' k (by linarith)])
        have hh₄ : (A ^ (3 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) / 3) ≤ (p' k ^ (3 : ℝ) + p' k ^ (3 * θ) + 1) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by norm_num [A_rpow_nonneg]) hh₂ (by norm_num)
        have hh₅ : (p' k ^ (3 : ℝ) + p' k ^ (3 * θ) + 1) ^ ((1 : ℝ) / 3) ≤ p' k * (1 + 2 * (p' k) ^ (3 * (θ - 1))) ^ ((1 : ℝ) / 3) := by
          calc
            (p' k ^ (3 : ℝ) + p' k ^ (3 * θ) + 1) ^ ((1 : ℝ) / 3) ≤ (p' k ^ (3 : ℝ) * (1 + 2 * (p' k) ^ (3 * (θ - 1)))) ^ ((1 : ℝ) / 3) := by
              apply Real.rpow_le_rpow _ hh₃ (by norm_num)
              apply add_nonneg _ (by norm_num)
              apply add_nonneg <;> apply Real.rpow_nonneg (by linarith [pgt1' k (by linarith)]) _
            _ = p' k * (1 + 2 * (p' k) ^ (3 * (θ - 1))) ^ ((1 : ℝ) / 3) := by
              rw [Real.mul_rpow _ _]
              simp
              left
              rw [← Real.rpow_mul _]
              simp
              linarith [p'pos k (by linarith)]
              apply Real.rpow_nonneg (by linarith [pgt1' k (by linarith)]) _
              apply add_nonneg
              linarith
              apply mul_nonneg
              linarith
              apply Real.rpow_nonneg (by linarith [pgt1' k (by linarith)]) _
        have hh₆ : (A ^ (3 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) / 3) ≤ p' k * (1 + 2 * (p' k) ^ (3 * (θ - 1))) ^ ((1 : ℝ) / 3) := by linarith [hh₄, hh₅]
        have hh₇ : (A ^ (3 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) / 3) = A ^ ((3 : ℝ) ^ k) := by
          rw [← Real.rpow_natCast _ (k + 1), ← Real.rpow_mul (by linarith [A_pow_nonneg 1]), Nat.cast_add, Real.rpow_add_nat (by linarith)]
          simp
        rw [← hh₇]
        exact hh₆
      have h₅ : (1 + 2 * (p' k) ^ (3 * (θ - 1))) ^ ((1 : ℝ) / 3) ≤ 1 + (p' k) ^ (3 * (θ - 1)) := by
        calc
          (1 + 2 * (p' k) ^ (3 * (θ - 1))) ^ ((1 : ℝ) / 3) ≤ 1 + 2 * (p' k) ^ (3 * (θ - 1)) / 3 := by
            rw [add_comm 1 (2 * p' k ^ (3 * (θ - 1)) / 3)]
            apply lem7' (2 * p' k ^ (3 * (θ - 1))) _
            apply mul_pos (by linarith)
            apply Real.rpow_pos_of_pos (by linarith [pgt1' k (by linarith)]) _
          _ ≤ 1 + (p' k) ^ (3 * (θ - 1)) := by
            simp; ring_nf;
            calc
              p' k ^ (-3 + θ * 3) * (2 / 3) ≤ p' k ^ (-3 + θ * 3) * 1 := by
                rw [mul_le_mul_left]; norm_num
                apply Real.rpow_pos_of_pos (by linarith [pgt1' k (by linarith)]) _
              _ ≤ p' k ^ (-3 + θ * 3) := by simp
      have h₆ : A ^ ((3 : ℝ) ^ k) ≤ p' k + (p' k) ^ (3 * θ - 2) := by
        calc
          A ^ ((3 : ℝ) ^ k) ≤ p' k * (1 + 2 * (p' k) ^ (3 * (θ - 1))) ^ ((1 : ℝ) / 3) := h₄
          _ ≤ p' k * (1 + (p' k) ^ (3 * (θ - 1))) := by apply mul_le_mul_of_nonneg_left h₅ (by linarith [pgt1' k (by linarith)])
          _ = p' k ^ 1 + (p' k) ^ (3 * θ - 2) := by
            ring_nf
            simp
            have : p' k * p' k ^ (-3 + θ * 3) = p' k ^ (1 : ℝ) * p' k ^ (-3 + θ * 3) := by simp
            rw [this]
            rw [← Real.rpow_add (p'pos k (by linarith)) 1 (-3 + θ * 3)]
            ring_nf
          _ = p' k + (p' k) ^ (3 * θ - 2) := by ring_nf
      have h₇ : |A ^ ((3 : ℝ) ^ k) - (p' k)| ≤ (p' k) ^ (-(2 - 3 * θ)) := by
        rw [abs_le']
        constructor
        · simp [sub_le_iff_le_add, add_comm]
          exact h₆
        · simp
          linarith [h₃]
      rw [← neg_mul, mul_assoc, mul_comm, mul_assoc, Real.exp_mul, Real.exp_log, Real.rpow_mul]
      have : p' k ^ (-(2 - 3 * θ)) ≤ (Nat.cast (p 1) ^ (3 : ℝ) ^ k) ^ (-((2 - 3 * θ) / 3)) := by
        calc
          (p' k) ^ (-(2 - 3 * θ)) ≤ ((p' 1) ^ ((3 : ℝ) ^ (k - 1))) ^ (-(2 - 3 * θ)) := by
            apply Real.rpow_le_rpow_of_nonpos
            apply Real.rpow_pos_of_pos (by linarith [pgt1' 1 (by linarith)])
            have hhh : k - 1 + 1 = k := by apply Nat.sub_add_cancel; linarith
            have hhh' : p' 1 ^ (3 : ℝ) ^ (k - 1) ≤ p' (k - 1 + 1) := by
              apply lem7'''' (k - 1)
            rw [hhh] at hhh'
            assumption
            rw [θ]
            norm_num
          _ = ((p' 1) ^ ((3 : ℝ) ^ k / 3)) ^ (-(2 - 3 * θ)) := by
            have : ((3 : ℝ) ^ (k - 1)) = ((3 : ℝ) ^ k / 3) := by
              field_simp
              rw [← Real.rpow_natCast, ← Real.rpow_add_one (by norm_num) ↑(k - 1), Nat.cast_sub]
              ring_nf
              rw [← Real.rpow_natCast]
              linarith
            rw [this]
          _ = ((p' 1) ^ ((3 : ℝ) ^ k)) ^ (-(2 - 3 * θ) / 3) := by
            ring_nf
            rw [Real.rpow_mul, ← Real.rpow_mul]
            ring_nf
            apply Real.rpow_nonneg (by linarith [pgt1' 1 (by linarith)])
            linarith [pgt1' 1 (by linarith)]
          _ = (Nat.cast (p 1) ^ ((3 : ℝ) ^ k)) ^ (-(2 - 3 * θ) / 3) := by rw [p']
          _ = (Nat.cast (p 1) ^ (3 : ℝ) ^ k) ^ (-((2 - 3 * θ) / 3)) := by rw [neg_div]
      calc
        |A ^ (3 : ℝ) ^ k - p' k| ≤ p' k ^ (-(2 - 3 * θ)) := h₇
        _ ≤ (Nat.cast (p 1) ^ (3 : ℝ) ^ k) ^ (-((2 - 3 * θ) / 3)) := this
      linarith [p'pos 1]
      have : ((p 1) : ℝ) = p' 1 := by rw [p']
      rw [this]
      linarith [p'pos 1 (by linarith)]

noncomputable def min_dist (x : ℝ) : ℝ := |x - round x|

lemma min_dist_fract (x : ℝ) : min_dist x = min (Int.fract x) (1 - Int.fract x) := abs_sub_round_eq_min x

lemma floor_cast (x : ℝ) (xpos : 0 ≤ x) : (Nat.cast : ℕ → ℝ) (Nat.floor x) = (Int.cast : ℤ → ℝ) (Int.floor x) := by
  apply natCast_floor_eq_intCast_floor
  exact xpos

-- Nat.floorにする必要ある？Int.floorでもいい？
lemma min_dist_floor (x : ℝ) (xpos : 0 ≤ x) : min_dist x ≤ |x - Nat.floor x| := by
  rw [natCast_floor_eq_intCast_floor xpos, min_dist_fract, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg x)]
  exact min_le_left _ _

-- notation: "∥" x "∥" => min_dist A

-- n₀は実数が本来かもしれないが、こっちも出るはず
axiom Mahler (r : ℚ) (ε : ℝ) (h₁ : 1 < r) (h₂ : ∀ n : ℤ, ↑n ≠ r) :
∃ n₀ : ℕ, n₀ > 0 ∧ ∀ n ≥ n₀, min_dist (r ^ (n : ℝ)) > Real.exp (-ε * (n : ℝ))


-- Aが自然数ならp1=A^3がそもそも素数ではないのでは？A>1も合わせる。元の証明より簡単にはなる？
lemma A_not_nat : ∀ n : ℕ, A ≠ n := by
  intro n h
  have : p 1 = n ^ 3 :=  by
    simp [p, h]
    rw [← Real.rpow_natCast, ← cast_nat_pow_eq_rpow_cast, Nat.floor_coe]; simp
  have : ¬Nat.Prime (p 1) := by rw [this]; exact Nat.Prime.not_prime_pow (by simp)
  have : Nat.Prime (p 1) := prime_seq' 1 (by linarith)
  contradiction

lemma nat_pos (r : ℚ) (h : 1 < r) (n : ℤ) (hn : n = r) : n ∈ Set.range Nat.cast := by
  rw [← hn] at h
  apply Int.cast_lt.mp at h
  have h' : 0 ≤ n := by
    calc
      0 ≤ Int.ofNat 1 := by norm_num
      _ ≤ n := le_of_lt h
  rcases Int.eq_ofNat_of_zero_le h' with ⟨m, hm⟩
  exact ⟨m, hm.symm⟩

theorem Mills_irrational : Irrational A := by
  rw [Irrational]; simp
  intro r h
  have h₁ : 1 < r := by
    have : Rat.cast 1  < (r : ℝ) := by rw [h]; simp; exact Mills_exists.left
    apply Rat.cast_lt.1 this
  have h₂ : ∀ n : ℤ, ↑n ≠ r := by
    intro n h₃
    rcases (nat_pos r h₁ n h₃) with ⟨m, hm⟩
    rw [← h₃, ← hm] at h
    apply A_not_nat m h.symm
  rcases lem7 with ⟨γ, _, k₁, _, h₃⟩
  rcases Mahler r γ h₁ h₂ with ⟨K, h₄⟩
  let k := max K k₁
  have h₅ : K ≤ 3 ^ k := by
    calc
      K ≤ k := le_max_left K k₁
      _ ≤ 3 ^ k := by apply le_of_lt (Nat.lt_pow_self (by norm_num) k)
  have h₆ : min_dist (r ^ 3 ^ k) > Real.exp (-γ * 3 ^ k) := by
    have : Nat.pow 3 k = (3 : ℝ) ^ k := by simp -- 抽象化
    calc
      min_dist (r ^ 3 ^ k) = min_dist (r ^ (3 ^ k : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_natCast]; simp
      _ > Real.exp (-γ * 3 ^ k) := by rw [← this]; apply h₄.right (3 ^ k) h₅
  have h₇ : min_dist (r ^ 3 ^ k) ≤ Real.exp (-γ * 3 ^ k) := by
    calc
      min_dist (r ^ 3 ^ k) ≤ |(r : ℝ) ^ 3 ^ k - Nat.floor ((r : ℝ) ^ 3 ^ k)| := by
        apply min_dist_floor
        rw [h, ← Real.rpow_natCast]
        apply Real.rpow_nonneg (by linarith [Mills_gt_one])
      _ = |A ^ 3 ^ k - Nat.floor (A ^ 3 ^ k)| := by rw [h]
      _ = |A ^ (3 : ℝ) ^ k - Nat.floor (A ^ (3 : ℝ) ^ k)| := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        have : (Nat.cast : ℕ → ℝ) (Nat.pow 3 k) = (3 : ℝ) ^ (k : ℝ) := by simp --抽象化
        rw [← this]; simp
      _ = |A ^ (3 : ℝ) ^ k - p' k| := by rw [p'eqp''', p''', ← Real.rpow_natCast]
      _ ≤ Real.exp (-γ * 3 ^ k) := h₃ k (le_max_right K k₁)
  linarith
-/
