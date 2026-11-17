import TauFourthExponent
import TauFourthExceptions
import TauExponent
import TauPowerInvert

namespace TauFourthLayer

/-- Conditional fourth layer estimate for any sequence having the Hecke
recurrence at fourth prime powers. This does not assert that tauTruncated has
the recurrence. -/
theorem layer_bound (habc : TauTarget.abcConjecture) (t : ℕ → ℤ)
    (hrec : ∀ p : ℕ, p.Prime → t (p^4) = TauArithmetic.hecke (t p) p 4) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ X : ℕ, N ≤ X →
        ((TauAssembly.layer t X 2).card : ℝ) ≤
          C * Real.rpow (X : ℝ) (1 / 10 + ε) := by
  apply TauFourthExceptions.layer_power_bound_from_nonexceptional_bases t (1/10) (by norm_num)
  intro ε hε
  obtain ⟨δ, hδ, h9, h10, _, hratio⟩ := TauExponent.choose_delta_for_low_layers ε hε
  have hδsmall : δ < 1 := by linarith
  obtain ⟨C, hC, hpower⟩ := TauFourthExponent.pointwise_power habc δ hδ hδsmall
  refine ⟨Real.rpow C (1 / (10-12*δ)), Real.rpow_pos_of_pos hC _, 1, ?_⟩
  intro X hX p hp hp2 hprime hne5 hvalle
  let l := (t (p^4)).natAbs
  have hl : l.Prime := hprime
  have hl5 : l ≠ 5 := hne5
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hv : (TauArithmetic.hecke (t p) p 4).natAbs = l := by
    dsimp [l]
    rw [hrec p hp]
  have hpoint := hpower p l (t p) hp hl hpodd hl5 hv
  have hXreal : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlreal : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hle : (l : ℝ) ≤ X := by exact_mod_cast hvalle
  have hmon : Real.rpow (l : ℝ) (1+δ) ≤ Real.rpow (X : ℝ) (1+δ) :=
    Real.rpow_le_rpow hlreal hle (by linarith)
  have hpointX : Real.rpow (p : ℝ) (10-12*δ) ≤ C * Real.rpow (X : ℝ) (1+δ) :=
    le_trans hpoint (mul_le_mul_of_nonneg_left hmon (le_of_lt hC))
  exact TauPowerInvert.bound_base_by_target (p : ℝ) (X : ℝ) C (10-12*δ) (1+δ) (1/10+ε)
    (by exact_mod_cast hp.pos) hXreal hC h10 hratio hpointX

end TauFourthLayer

#print axioms TauFourthLayer.layer_bound
