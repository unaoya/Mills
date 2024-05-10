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

noncomputable def NNReal.pnpow (x : ℝ≥0) (n : ℕ+) : ℝ≥0 := x ^ ((Nat.cast : ℕ → ℝ) n)

noncomputable def Mills_seq (x : ℝ≥0) (n : ℕ+) : ℕ := Nat.floor (x.pnpow (3 ^ n.val))

def Mills (x : ℝ≥0) : Prop := 1 < x ∧ ∀ n : ℕ+, Nat.Prime (Mills_seq x n)

def W := {x | Mills x}

noncomputable def A : ℝ≥0 := sInf W
