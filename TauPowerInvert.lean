import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Invert an inequality of positive real powers. -/

namespace TauPowerInvert

theorem bound_base_from_power (p X C a b : ℝ)
    (hp : 0 < p) (hX : 0 < X) (hC : 0 < C) (ha : 0 < a)
    (h : Real.rpow p a ≤ C * Real.rpow X b) :
    p ≤ Real.rpow C (1 / a) * Real.rpow X (b / a) := by
  have ha_inv : 0 ≤ 1 / a := by positivity
  have hpow := Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hp a)) h ha_inv
  have hleft : Real.rpow (Real.rpow p a) (1 / a) = p := by
    change (p ^ a) ^ (1 / a) = p
    rw [← Real.rpow_mul (le_of_lt hp)]
    have hmul : a * (1 / a) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  have hright : Real.rpow (C * Real.rpow X b) (1 / a) =
      Real.rpow C (1 / a) * Real.rpow X (b / a) := by
    change (C * X ^ b) ^ (1 / a) = C ^ (1 / a) * X ^ (b / a)
    rw [Real.mul_rpow (le_of_lt hC) (le_of_lt (Real.rpow_pos_of_pos hX b)),
      ← Real.rpow_mul (le_of_lt hX)]
    congr 1
    ring
  change Real.rpow (Real.rpow p a) (1 / a) ≤
    Real.rpow (C * Real.rpow X b) (1 / a) at hpow
  rwa [hleft, hright] at hpow

theorem bound_base_by_target (p X C a b θ : ℝ)
    (hp : 0 < p) (hX : 1 ≤ X) (hC : 0 < C) (ha : 0 < a)
    (hratio : b / a ≤ θ)
    (h : Real.rpow p a ≤ C * Real.rpow X b) :
    p ≤ Real.rpow C (1 / a) * Real.rpow X θ := by
  have hXpos : 0 < X := by linarith
  have h1 := bound_base_from_power p X C a b hp hXpos hC ha h
  have h2 : Real.rpow X (b / a) ≤ Real.rpow X θ :=
    Real.rpow_le_rpow_of_exponent_le hX hratio
  exact h1.trans (mul_le_mul_of_nonneg_left h2
    (le_of_lt (Real.rpow_pos_of_pos hC _)))

end TauPowerInvert

#print axioms TauPowerInvert.bound_base_from_power
#print axioms TauPowerInvert.bound_base_by_target
