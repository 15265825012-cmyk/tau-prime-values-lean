import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Exact exponent selection for the two elementary `abc`-based reductions.
This file proves only the inequalities between real exponents.  It does not
state or assume the `abc` conjecture, nor does it define Ramanujan's tau.
-/

namespace TauExponent

theorem choose_delta_for_low_layers (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ 9 - 13 * δ > 0 ∧ 10 - 12 * δ > 0 ∧
      2 * (1 + δ) / (9 - 13 * δ) ≤ 2 / 9 + ε ∧
      (1 + δ) / (10 - 12 * δ) ≤ 1 / 10 + ε := by
  let δ : ℝ := min (1 / 100 : ℝ) (ε / 10)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (by positivity)
  have hδsmall : δ ≤ 1 / 100 := by
    exact min_le_left _ _
  have hδε : δ ≤ ε / 10 := by
    exact min_le_right _ _
  have h9 : 0 < 9 - 13 * δ := by nlinarith
  have h10 : 0 < 10 - 12 * δ := by nlinarith
  have hprod : ε * δ ≤ ε / 100 := by
    have := mul_le_mul_of_nonneg_left hδsmall (le_of_lt hε)
    nlinarith
  refine ⟨δ, hδ, h9, h10, ?_, ?_⟩
  · apply (div_le_iff₀ h9).2
    nlinarith
  · apply (div_le_iff₀ h10).2
    nlinarith

end TauExponent

#print axioms TauExponent.choose_delta_for_low_layers
