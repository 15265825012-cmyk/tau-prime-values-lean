import TauAssembly
import TauDefinition
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Statement-only formalization of the exact target.  No theorem asserting this
proposition is proved here.  `tauTruncated` is the n-th coefficient of the
finite product through n; its bridge to the infinite discriminant product is
not supplied by this file.
-/

namespace TauTarget

/-- Product of the distinct rational prime factors of a positive integer. -/
noncomputable def radical (n : ℕ) : ℕ :=
  n.primeFactors.prod id

/-- The positive-integer `abc` conjecture.  For positive coprime `a`, `b`
    with `a+b=c`, the quantity `c` is the largest member of the triple. -/
def abcConjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ C * Real.rpow (radical (a * b * c) : ℝ) (1 + δ)

/-- Distinct positive prime values of the finite-coefficient tau sequence,
    counted with absolute value and bounded by the natural-number X. -/
noncomputable def tauPrimeValues (X : ℕ) : Finset ℕ :=
  TauAssembly.primeValues tauTruncated X

/-- The proposed exponent 2/9+epsilon bound, pointwise for large integer X. -/
def desiredBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
    ∀ X : ℕ, N ≤ X →
      ((tauPrimeValues X).card : ℝ) ≤
        C * Real.rpow (X : ℝ) ((2 : ℝ) / 9 + ε)

/-- This is a proposition, not a proved theorem. -/
def conditionalGoal : Prop := abcConjecture → desiredBound

end TauTarget

#print axioms TauTarget.conditionalGoal
