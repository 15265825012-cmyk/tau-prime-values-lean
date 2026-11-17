import TauAbcAlgebra
import Mathlib.Tactic

namespace TauFourthExtract

theorem remove_auxiliary_power (u Q K δ : ℝ)
    (hu : 0 < u) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (h : u^2 ≤ K * Real.rpow (Q*u) (1+δ)) :
    Real.rpow u (1-δ) ≤ K * Real.rpow Q (1+δ) := by
  have hid : Real.rpow u (1-δ) * Real.rpow u (1+δ) = u^2 := by
    have he : (1-δ)+(1+δ) = (2 : ℝ) := by ring
    calc
      _ = Real.rpow u ((1-δ)+(1+δ)) := (Real.rpow_add hu (1-δ) (1+δ)).symm
      _ = u^2 := by rw [he]; norm_num
  have hprod : Real.rpow (Q*u) (1+δ) =
      Real.rpow Q (1+δ) * Real.rpow u (1+δ) :=
    Real.mul_rpow hQ (le_of_lt hu)
  have hineq : Real.rpow u (1-δ) * Real.rpow u (1+δ) ≤
      (K * Real.rpow Q (1+δ)) * Real.rpow u (1+δ) := by
    rw [hid]
    rw [hprod] at h
    nlinarith
  exact le_of_mul_le_mul_right hineq (Real.rpow_pos_of_pos hu (1+δ))

end TauFourthExtract

#print axioms TauFourthExtract.remove_auxiliary_power
