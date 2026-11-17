import TauAbcAlgebra
import TauPowerInvert
import Mathlib.Tactic.Linarith

/-! Pointwise exponent extraction, conditional on the two input inequalities. -/

namespace TauPointwiseAlgebra

theorem bound_of_auxiliary_estimates
    (p X y K C δ r θ : ℝ)
    (hp : 0 < p) (hX : 1 ≤ X) (hy : 0 < y) (hK : 0 < K) (hC : 0 < C)
    (hδ : δ < 1)
    (ha : 0 < r * (1 - δ) - (1 + δ))
    (hratio : (1 + δ) / (r * (1 - δ) - (1 + δ)) ≤ θ)
    (h_lower : Real.rpow p r ≤ K * y)
    (h_upper : Real.rpow y (1 - δ) ≤ C * Real.rpow (p * X) (1 + δ)) :
    p ≤ Real.rpow (Real.rpow K (1 - δ) * C)
        (1 / (r * (1 - δ) - (1 + δ))) * Real.rpow X θ := by
  have hXpos : 0 < X := by linarith
  have hbase := TauAbcAlgebra.abc_general_exponent p X y K C δ r hp hXpos hy hK hδ
    h_lower h_upper
  have hnewC : 0 < Real.rpow K (1 - δ) * C :=
    mul_pos (Real.rpow_pos_of_pos hK _) hC
  exact TauPowerInvert.bound_base_by_target p X (Real.rpow K (1 - δ) * C)
    (r * (1 - δ) - (1 + δ)) (1 + δ) θ hp hX hnewC ha hratio hbase

end TauPointwiseAlgebra

#print axioms TauPointwiseAlgebra.bound_of_auxiliary_estimates
