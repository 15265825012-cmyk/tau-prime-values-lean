import TauArithmetic
import Mathlib.Tactic

namespace TauFourthBranch

/-- Completing the square gives either a direct small-base bound or a lower
bound on the auxiliary variable, with no use of Deligne's bound. -/
theorem small_or_auxiliary_large (a : ℤ) (p l : ℕ)
    (hv : (TauArithmetic.hecke a p 4).natAbs = l) :
    let u : ℕ := (2 * a^2 - 3 * (p : ℤ)^11).natAbs
    p^22 ≤ l ∨ p^11 ≤ u := by
  let u : ℕ := (2 * a^2 - 3 * (p : ℤ)^11).natAbs
  let z : ℤ := TauArithmetic.hecke a p 4
  have hz : z.natAbs = l := hv
  have hzlo : -(l : ℤ) ≤ z := by
    have h := neg_abs_le z
    simpa [← Int.natCast_natAbs, hz] using h
  have hsq : ((u : ℤ)^2) = (2 * a^2 - 3 * (p : ℤ)^11)^2 := by
    simp [u, sq_abs]
  have heq : (u : ℤ)^2 = 5 * (p : ℤ)^22 + 4*z := by
    rw [hsq, TauArithmetic.complete_square, ← TauArithmetic.hecke_four]
  by_cases hsmall : p^22 ≤ l
  · exact Or.inl hsmall
  · refine Or.inr ?_
    have hlarge : (l : ℤ) ≤ (p : ℤ)^22 := by
      exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hsmall))
    have hp22 : (p : ℤ)^22 = ((p : ℤ)^11)^2 := by ring
    have hu_nonneg : 0 ≤ (u : ℤ) := by positivity
    have hp_nonneg : 0 ≤ (p : ℤ)^11 := by positivity
    have hu_ge : (p : ℤ)^11 ≤ (u : ℤ) := by
      rw [hp22] at heq hlarge
      nlinarith
    exact_mod_cast hu_ge

end TauFourthBranch

#print axioms TauFourthBranch.small_or_auxiliary_large
