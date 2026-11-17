import TauFourthAbc
import TauFourthBranch
import TauFourthExtract

namespace TauFourthExponent

/-- Pointwise p-power consequence of abc for an abstract Hecke fourth
coefficient. The exceptional value l=5 is excluded explicitly. -/
theorem pointwise_power (habc : TauTarget.abcConjecture)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p l : ℕ) (a : ℤ),
      p.Prime → l.Prime → Odd p → l ≠ 5 →
      (TauArithmetic.hecke a p 4).natAbs = l →
      Real.rpow (p : ℝ) (10 - 12 * δ) ≤ C * Real.rpow (l : ℝ) (1 + δ) := by
  obtain ⟨K, hK, habound⟩ := TauFourthAbc.abc_hecke_fourth_bound habc δ hδ
  let D := K * Real.rpow 10 (1 + δ)
  have hD : 0 < D := by dsimp [D]; positivity
  let C := max D 1
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hDC : D ≤ C := le_max_left _ _
  have h1C : 1 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro p l a hp hl hodd hl5 hv
  let u : ℕ := (2*a^2 - 3*(p : ℤ)^11).natAbs
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.pos
  have halt := TauFourthBranch.small_or_auxiliary_large a p l hv
  change p^22 ≤ l ∨ p^11 ≤ u at halt
  rcases halt with hsmall | hlarge
  · have hp_pow : Real.rpow (p : ℝ) (10-12*δ) ≤ (p : ℝ)^22 := by
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : 10 - 12*δ ≤ 22)
      simpa using h
    have hp_small : (p : ℝ)^22 ≤ l := by exact_mod_cast hsmall
    have hl_pow : (l : ℝ) ≤ Real.rpow (l : ℝ) (1+δ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hl1 (by linarith : (1 : ℝ) ≤ 1+δ)
      simpa using h
    have hnonneg : 0 ≤ Real.rpow (l : ℝ) (1+δ) := Real.rpow_nonneg (Nat.cast_nonneg l) _
    nlinarith
  · have hu_nat : 0 < u := lt_of_lt_of_le (pow_pos hp.pos _) hlarge
    have hu : (0 : ℝ) < u := by exact_mod_cast hu_nat
    have hreal : (u : ℝ)^2 ≤ K * Real.rpow ((10 : ℝ)*p*l*u) (1+δ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using habound p l a hp hl hodd hl5 hv
    have haux := TauFourthExtract.remove_auxiliary_power (u : ℝ) (10*(p : ℝ)*l) K δ hu (by positivity) (le_of_lt hK) hreal
    have hsplit : Real.rpow (10*(p : ℝ)*l) (1+δ) =
        Real.rpow 10 (1+δ) * Real.rpow ((p : ℝ)*l) (1+δ) := by
      rw [show (10 : ℝ)*(p : ℝ)*l = 10*((p : ℝ)*l) by ring]
      exact Real.mul_rpow (by norm_num) (by positivity)
    have hupp : Real.rpow (u : ℝ) (1-δ) ≤ D * Real.rpow ((p : ℝ)*l) (1+δ) := by
      rw [hsplit] at haux
      simpa only [D, mul_assoc] using haux
    have hlow : Real.rpow (p : ℝ) (11 : ℝ) ≤ 1 * (u : ℝ) := by
      have hl' : (p : ℝ)^11 ≤ u := by exact_mod_cast hlarge
      simpa using hl'
    have hmain := TauAbcAlgebra.abc_general_exponent (p : ℝ) (l : ℝ) (u : ℝ) 1 D δ 11
      hpR hlR hu (by norm_num) hδsmall hlow hupp
    have hmain' : Real.rpow (p : ℝ) (10 - 12*δ) ≤ D * Real.rpow (l : ℝ) (1+δ) := by
      convert hmain using 1 <;> simp <;> ring
    exact le_trans hmain' (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg (Nat.cast_nonneg l) _))

end TauFourthExponent

#print axioms TauFourthExponent.pointwise_power
