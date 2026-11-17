import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Interval

/-!
# Finite coefficient definition of the Ramanujan tau sequence

The n-th coefficient of q * product_{j >= 1} (1 - q^j)^24 can be
computed from factors with j <= n.  This file defines that finite
coefficient.  The bridge to an infinite formal power series, as well as
the Hecke, parity and Deligne properties, are not asserted here.
-/

noncomputable def tauTruncated (n : ℕ) : ℤ :=
  (((Polynomial.X : Polynomial ℤ) *
    ∏ j ∈ Finset.Icc 1 n, (1 - Polynomial.X ^ j) ^ 24)).coeff n

theorem tauTruncated_zero : tauTruncated 0 = 0 := by
  simp [tauTruncated]

theorem tauTruncated_one : tauTruncated 1 = 1 := by
  simp only [tauTruncated, Finset.Icc_self, Finset.prod_singleton,
    pow_one, Polynomial.coeff_X_mul]
  change Polynomial.constantCoeff ((1 - Polynomial.X : Polynomial ℤ) ^ 24) = 1
  rw [map_pow]
  have h : Polynomial.constantCoeff (1 - Polynomial.X : Polynomial ℤ) = 1 := by
    change ((1 - Polynomial.X : Polynomial ℤ).coeff 0) = 1
    simp
  rw [h, one_pow]

#print axioms tauTruncated_zero
#print axioms tauTruncated_one
