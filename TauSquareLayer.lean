import TauSquareHecke
import TauExponent
import TauPointwiseAlgebra
import TauLayerBridge
import Mathlib.Tactic.FieldSimp

/-! A square-layer counting theorem from abc and a supplied Hecke identity.
The Hecke identity is an explicit input for the sequence, not a claim that
the finite q-product has already been connected to modular forms. -/
namespace TauSquareLayer

theorem square_base_bound (t : ℕ → ℤ)
    (habc : TauTarget.abcConjecture)
    (hhecke : ∀ p : ℕ, p.Prime →
      t (p ^ 2) = TauArithmetic.hecke (t p) (p : ℤ) 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ X : ℕ, N ≤ X → ∀ p : ℕ, p.Prime →
        ((t (p ^ 2)).natAbs).Prime →
        (t (p ^ 2)).natAbs ≤ X →
        (p : ℝ) ≤ C * Real.rpow (X : ℝ) (2 / 9 + ε) := by
  intro ε hε
  obtain ⟨δ, hδ, h9, h10, hratio0, hratio4⟩ := TauExponent.choose_delta_for_low_layers ε hε
  obtain ⟨K, hK, hbound⟩ := TauSquareHecke.hecke_square_abc_and_branch habc δ hδ
  have hδ1 : δ < 1 := by linarith
  have hden : (11 / 2 : ℝ) * (1 - δ) - (1 + δ) = (9 - 13 * δ) / 2 := by ring
  have ha : 0 < (11 / 2 : ℝ) * (1 - δ) - (1 + δ) := by rw [hden]; linarith
  have hratio : (1 + δ) / ((11 / 2 : ℝ) * (1 - δ) - (1 + δ)) ≤ 2 / 9 + ε := by
    rw [hden]
    have hid : (1 + δ) / ((9 - 13 * δ) / 2) = 2 * (1 + δ) / (9 - 13 * δ) := by
      field_simp
    rw [hid]
    exact hratio0
  let Csmall : ℝ := Real.rpow 2 (1 / 11)
  let Clarge : ℝ := Real.rpow (Real.rpow 2 (1 - δ) * K)
      (1 / ((11 / 2 : ℝ) * (1 - δ) - (1 + δ)))
  have hCs : 0 < Csmall := Real.rpow_pos_of_pos (by norm_num) _
  have hCl : 0 < Clarge := Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hK) _
  refine ⟨Csmall + Clarge, by positivity, 1, ?_⟩
  intro X hX p hp hlPrime hlX
  let l := (t (p ^ 2)).natAbs
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hXR : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXR0 : 0 < (X : ℝ) := by linarith
  have hlR : (l : ℝ) ≤ (X : ℝ) := by exact_mod_cast hlX
  have hval : (TauArithmetic.hecke (t p) (p : ℤ) 2).natAbs = l := by
    dsimp [l]
    rw [← hhecke p hp]
  have ⟨hupper, hbranch⟩ := hbound (t p) p l (X : ℝ) hp hlPrime hXR0 hlR hval
  have hy : 0 < ((t p).natAbs : ℝ) := by
    exact_mod_cast (TauSquareHecke.square_inputs (t p) p l hp hlPrime hval).1
  have hxp : 0 ≤ Real.rpow (X : ℝ) (2 / 9 + ε) :=
    le_of_lt (Real.rpow_pos_of_pos hXR0 _)
  rcases hbranch with hsmall | hlarge
  · have hs : Real.rpow (p : ℝ) 11 ≤ 2 * Real.rpow (X : ℝ) 1 := by
      have hp11 : Real.rpow (p : ℝ) 11 = (p : ℝ) ^ 11 := Real.rpow_natCast _ 11
      have hXone : Real.rpow (X : ℝ) 1 = (X : ℝ) := Real.rpow_one _
      rw [hp11, hXone]
      exact hsmall
    have hsmallRatio : (1 : ℝ) / 11 ≤ 2 / 9 + ε := by linarith
    have hb := TauPowerInvert.bound_base_by_target (p : ℝ) (X : ℝ) 2 11 1 (2 / 9 + ε)
      hpR hXR (by norm_num) (by norm_num) hsmallRatio hs
    have hCs' : Csmall ≤ Csmall + Clarge := by linarith
    exact hb.trans (mul_le_mul_of_nonneg_right hCs' hxp)
  · have hb := TauPointwiseAlgebra.bound_of_auxiliary_estimates (p : ℝ) (X : ℝ)
      ((t p).natAbs : ℝ) 2 K δ (11 / 2) (2 / 9 + ε)
      hpR hXR hy (by norm_num) hK hδ1 ha hratio hlarge hupper
    have hCl' : Clarge ≤ Csmall + Clarge := by linarith
    exact hb.trans (mul_le_mul_of_nonneg_right hCl' hxp)

theorem square_layer_bound (t : ℕ → ℤ)
    (habc : TauTarget.abcConjecture)
    (hhecke : ∀ p : ℕ, p.Prime →
      t (p ^ 2) = TauArithmetic.hecke (t p) (p : ℤ) 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ X : ℕ, N ≤ X →
        ((TauAssembly.layer t X 1).card : ℝ) ≤
          C * Real.rpow (X : ℝ) (2 / 9 + ε) := by
  apply TauLayerBridge.layer_power_bound_from_base_power_bound t 1 (2 / 9) (by norm_num)
  simpa only [mul_one] using square_base_bound t habc hhecke

end TauSquareLayer

#print axioms TauSquareLayer.square_base_bound
#print axioms TauSquareLayer.square_layer_bound
