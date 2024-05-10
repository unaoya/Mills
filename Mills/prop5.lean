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

-- 補題として1より大きい自然数nに対して(n+1)^3-1が合成数となることを示しておく。
lemma not_prime (n : ℕ) (nge2 : 2 ≤ n) : ¬Nat.Prime ((n + 1) ^ 3 - 1) := by
  have h' : (n + 1) ^ 3 - 1 = n * (n ^ 2 + 3 * n + 3) := by
    ring_nf; rw [add_assoc, add_assoc, add_assoc, Nat.add_sub_self_left]
  rw [h']
  apply Nat.not_prime_mul (by linarith) (by simp)
