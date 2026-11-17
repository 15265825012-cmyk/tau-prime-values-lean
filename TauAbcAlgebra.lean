import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Algebraic consequence of the two real inequalities in the p² `abc` layer.
No assertion about the `abc` conjecture or the arithmetic function τ is made. -/

namespace TauAbcAlgebra

theorem abc_square_exponent
    (p X y K C δ : ℝ)
    (hp : 0 < p) (hX : 0 < X) (hy : 0 < y) (hK : 0 < K)
    (hδ : δ < 1)
    (h_lower : Real.rpow p (11 / 2) ≤ K * y)
    (h_upper : Real.rpow y (1 - δ) ≤ C * Real.rpow (p * X) (1 + δ)) :
    Real.rpow p ((9 - 13 * δ) / 2) ≤
      (Real.rpow K (1 - δ) * C) * Real.rpow X (1 + δ) := by
  have hexp : (11 / 2 : ℝ) * (1 - δ) =
      ((9 - 13 * δ) / 2) + (1 + δ) := by ring
  have h_low : Real.rpow p ((9 - 13 * δ) / 2) * Real.rpow p (1 + δ) ≤
      Real.rpow K (1 - δ) * Real.rpow y (1 - δ) := by
    calc
      _ = Real.rpow p (((9 - 13 * δ) / 2) + (1 + δ)) :=
        (Real.rpow_add hp _ _).symm
      _ = Real.rpow p ((11 / 2) * (1 - δ)) := by rw [hexp]
      _ = Real.rpow (Real.rpow p (11 / 2)) (1 - δ) :=
        Real.rpow_mul (le_of_lt hp) _ _
      _ ≤ Real.rpow (K * y) (1 - δ) :=
        Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hp _)) h_lower (by linarith)
      _ = Real.rpow K (1 - δ) * Real.rpow y (1 - δ) :=
        Real.mul_rpow (le_of_lt hK) (le_of_lt hy)
  have hKpow : 0 ≤ Real.rpow K (1 - δ) :=
    le_of_lt (Real.rpow_pos_of_pos hK _)
  have hmain : Real.rpow p ((9 - 13 * δ) / 2) * Real.rpow p (1 + δ) ≤
      (Real.rpow K (1 - δ) * C * Real.rpow X (1 + δ)) * Real.rpow p (1 + δ) := by
    calc
      _ ≤ Real.rpow K (1 - δ) * Real.rpow y (1 - δ) := h_low
      _ ≤ Real.rpow K (1 - δ) * (C * Real.rpow (p * X) (1 + δ)) :=
        mul_le_mul_of_nonneg_left h_upper hKpow
      _ = (Real.rpow K (1 - δ) * C * Real.rpow X (1 + δ)) * Real.rpow p (1 + δ) := by
        have hmul : Real.rpow (p * X) (1 + δ) =
            Real.rpow p (1 + δ) * Real.rpow X (1 + δ) :=
          Real.mul_rpow (le_of_lt hp) (le_of_lt hX)
        rw [hmul]
        ring
  exact le_of_mul_le_mul_right hmain (Real.rpow_pos_of_pos hp (1 + δ))

theorem abc_general_exponent
    (p X y K C δ r : ℝ)
    (hp : 0 < p) (hX : 0 < X) (hy : 0 < y) (hK : 0 < K)
    (hδ : δ < 1)
    (h_lower : Real.rpow p r ≤ K * y)
    (h_upper : Real.rpow y (1 - δ) ≤ C * Real.rpow (p * X) (1 + δ)) :
    Real.rpow p (r * (1 - δ) - (1 + δ)) ≤
      (Real.rpow K (1 - δ) * C) * Real.rpow X (1 + δ) := by
  have hexp : r * (1 - δ) = (r * (1 - δ) - (1 + δ)) + (1 + δ) := by ring
  have h_low : Real.rpow p (r * (1 - δ) - (1 + δ)) * Real.rpow p (1 + δ) ≤
      Real.rpow K (1 - δ) * Real.rpow y (1 - δ) := by
    calc
      _ = Real.rpow p ((r * (1 - δ) - (1 + δ)) + (1 + δ)) :=
        (Real.rpow_add hp _ _).symm
      _ = Real.rpow p (r * (1 - δ)) := by congr 1 <;> ring
      _ = Real.rpow (Real.rpow p r) (1 - δ) := Real.rpow_mul (le_of_lt hp) _ _
      _ ≤ Real.rpow (K * y) (1 - δ) :=
        Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hp _)) h_lower (by linarith)
      _ = Real.rpow K (1 - δ) * Real.rpow y (1 - δ) :=
        Real.mul_rpow (le_of_lt hK) (le_of_lt hy)
  have hKpow : 0 ≤ Real.rpow K (1 - δ) := le_of_lt (Real.rpow_pos_of_pos hK _)
  have hmain : Real.rpow p (r * (1 - δ) - (1 + δ)) * Real.rpow p (1 + δ) ≤
      (Real.rpow K (1 - δ) * C * Real.rpow X (1 + δ)) * Real.rpow p (1 + δ) := by
    calc
      _ ≤ Real.rpow K (1 - δ) * Real.rpow y (1 - δ) := h_low
      _ ≤ Real.rpow K (1 - δ) * (C * Real.rpow (p * X) (1 + δ)) :=
        mul_le_mul_of_nonneg_left h_upper hKpow
      _ = (Real.rpow K (1 - δ) * C * Real.rpow X (1 + δ)) * Real.rpow p (1 + δ) := by
        have hmul : Real.rpow (p * X) (1 + δ) =
            Real.rpow p (1 + δ) * Real.rpow X (1 + δ) :=
          Real.mul_rpow (le_of_lt hp) (le_of_lt hX)
        rw [hmul]
        ring
  exact le_of_mul_le_mul_right hmain (Real.rpow_pos_of_pos hp (1 + δ))

end TauAbcAlgebra

#print axioms TauAbcAlgebra.abc_square_exponent
#print axioms TauAbcAlgebra.abc_general_exponent
