import Mills.Defs
import Mills.OLD_sequence

open Filter Topology NNReal

lemma aux (x : ℝ) (xpos : 1 < x) : x ^ 3 + x ^ 2 ≤ (x + 1) ^ 3 - 1 := by nlinarith

-- 定理3の冒頭の不等式。これは一般的に成り立つ。似た話を後でも使う？
lemma aux_ineq_in_thm3 (x : ℝ≥0) (xgt1 : 1 < x) :
    x ^ 3 + x ^ (3 * θ) < (x + 1) ^ 3 - 1 := by
  have : (3 * θ) < 2 := by rw [θ]; norm_num;
  calc
    x ^ 3 + x ^ (3 * θ) < x ^ 3 + x ^ 2 := by
      apply add_lt_add_left
      sorry
      -- apply Real.rpow_lt_rpow_of_exponent_lt
    _ = x ^ 3 + x ^ 2 := by simp
    _ ≤ (x + 1) ^ 3 - 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_sub _]; simp
      exact aux x.val xgt1
      calc
        1 ≤ x + 1 := by apply le_add_of_nonneg_left; simp
        _ ≤ (x + 1) ^ 3 := by apply le_self_pow; simp; simp

structure GoodPrimeSeq extends GoodSeq where
  prime (n : ℕ+) : Nat.Prime (seq n)

instance : CoeFun GoodPrimeSeq (fun _ => ℕ+ → ℕ+) := ⟨fun s => s.seq⟩

def NgeBHP : Type := {n : ℕ+ // BHP_const_pnat ≤ n}

/--
BHP定数より大きな素数。
作るべき数列の各項はこの条件を満たす。
-/
structure GoodPrime : Type where
  val : ℕ+
  gt : BHP_const_pnat ≤ val
  prime : Nat.Prime val

structure Step' (p q : GoodPrime) : Prop where
  h₀ : pnat_cube p.val ≤ q.val
  h₁ : q.val ≤ p.val ^ 3 + (p.val : ℝ).rpow (3 * θ)
  h₂ : q.val < pnat_cube (p.val + 1) - 1

lemma Stepex₀ (p : GoodPrime) : ∃ (q : GoodPrime), Step' p q := by sorry

/--
ℕじゃないものでも機能的に定義したいが。。
-/
noncomputable
def pp'' (p₀ : GoodPrime) : ℕ → GoodPrime
  | 0 => p₀
  | n + 1 => Classical.choose (Stepex₀ (pp'' p₀ n))

lemma hpp'' (p₀ : GoodPrime) (k : ℕ) : Step' (pp'' p₀ k) (pp'' p₀ (k + 1)) := by
  exact (Classical.choose_spec (Stepex₀ (pp'' p₀ k)))

noncomputable
def pp (p₀ : GoodPrime) : ℕ+ → GoodPrime := λ n => (pp'' p₀ n.natPred)

noncomputable
def ppp (p₀ : GoodPrime) (n : ℕ+) : GoodPrime :=
  match n.natPred with
  | 0 => p₀
  | k + 1 => Classical.choose (Stepex₀ (ppp p₀ ⟨k + 1, Nat.succ_pos'⟩))
    termination_by sorry

lemma hpp (p₀ : GoodPrime) (k : ℕ+) : Step' (pp p₀ k) (pp p₀ (k + 1)) := by
  unfold pp
  have : (k + 1).natPred = k.natPred + 1 := by
    simp
    exact rfl
  rw [this]
  apply hpp'' p₀ k.natPred

-- BHP定数より大きな素数を与えたら、そこからGPSを作る
noncomputable
def toGPS (p₀ : GoodPrime) : GoodPrimeSeq :=
{
  seq (n : ℕ+) := (pp p₀ n).val
  left (n : ℕ+) := (hpp p₀ n).h₀
  right (n : ℕ+) := (hpp p₀ n).h₂
  prime (n : ℕ+) := (pp p₀ n).prime
  seq1gt1 := by
    calc
      1 < 2 := by simp
      _ ≤ BHP_const_pnat := BHP_const_pnat_ge2
      _ ≤ p₀.val := p₀.gt
      _ = (pp p₀ 1).val := rfl
}

noncomputable
def Mills_seq (x : ℝ≥0) (n : ℕ+) : ℕ :=
  Nat.floor (x ^ (pnat_cube n))

/-古い定義-/
def Mills'' (x : ℝ≥0) : Prop := 1 < x ∧ ∀ n : ℕ+, Nat.Prime (Mills_seq x n)

theorem exists_Mills'' : ∃ A : ℝ≥0, Mills'' A := by
  set p := (toGPS ⟨BHP_const_pnat, (by simp), sorry⟩)
  set q := p.toGoodSeq
  use q.left_lim
  constructor
  · apply p.left_lim_gt_1
  · intro n
    rw [Mills_seq, q.left_floor_eq_seq]
    exact p.prime n

theorem exists_Mills : ∃ A : ℝ≥0, Mills A := by
  obtain ⟨A, hA⟩ := exists_Mills''
  use A
  constructor
  · exact hA.1
  · intro n hn
    exact hA.2 ⟨n, hn⟩
