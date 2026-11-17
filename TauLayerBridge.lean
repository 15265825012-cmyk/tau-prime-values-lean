import TauAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
Finite cardinality bridge: a pointwise bound on the prime base of a
Hecke-power layer bounds the number of distinct output values. The pointwise
bound is an explicit hypothesis, not derived from `abc` in this file.
-/

namespace TauLayerBridge

theorem layer_card_le_base_bound
    (t : ℕ → ℤ) (X k P : ℕ)
    (hbound : ∀ p : ℕ, Nat.Prime p →
      ((t (p ^ (2 * k))).natAbs).Prime →
      (t (p ^ (2 * k))).natAbs ≤ X → p ≤ P) :
    (TauAssembly.layer t X k).card ≤ P + 1 := by
  classical
  let values := (Finset.range (P + 1)).image (fun p => (t (p ^ (2 * k))).natAbs)
  have hsub : TauAssembly.layer t X k ⊆ values := by
    intro ell hell
    simp only [TauAssembly.layer, Finset.mem_filter, Finset.mem_range] at hell
    obtain ⟨hell_lt, hell_prime, p, hp, hpval⟩ := hell
    have hpval_prime : ((t (p ^ (2 * k))).natAbs).Prime := by
      simpa only [hpval] using hell_prime
    have hpval_le : (t (p ^ (2 * k))).natAbs ≤ X := by
      rw [hpval]
      omega
    have hp_le := hbound p hp hpval_prime hpval_le
    show ell ∈ values
    exact Finset.mem_image.mpr ⟨p, Finset.mem_range.mpr (by omega), hpval⟩
  calc
    (TauAssembly.layer t X k).card ≤ values.card := Finset.card_le_card hsub
    _ ≤ (Finset.range (P + 1)).card := Finset.card_image_le
    _ = P + 1 := Finset.card_range _

/-- A pointwise real-power bound for every contributing prime base gives the
    same exponent for the number of distinct prime values. -/
theorem layer_power_bound_from_base_power_bound
    (t : ℕ → ℤ) (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hbase : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ X : ℕ, N ≤ X → ∀ p : ℕ, p.Prime →
        ((t (p ^ (2 * k))).natAbs).Prime →
        (t (p ^ (2 * k))).natAbs ≤ X →
        (p : ℝ) ≤ C * Real.rpow (X : ℝ) (θ + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ X : ℕ, N ≤ X →
        ((TauAssembly.layer t X k).card : ℝ) ≤
          C * Real.rpow (X : ℝ) (θ + ε) := by
  intro ε hε
  obtain ⟨C, hC, N, hN⟩ := hbase ε hε
  refine ⟨C + 1, by linarith, N + 1, ?_⟩
  intro X hX
  have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hw : 1 ≤ Real.rpow (X : ℝ) (θ + ε) :=
    Real.one_le_rpow hx1 (by linarith)
  let P : ℕ := ⌊C * Real.rpow (X : ℝ) (θ + ε)⌋₊
  have hP : ∀ p : ℕ, p.Prime → ((t (p ^ (2 * k))).natAbs).Prime →
      (t (p ^ (2 * k))).natAbs ≤ X → p ≤ P := by
    intro p hp hprime hle
    exact Nat.le_floor (hN X (by omega) p hp hprime hle)
  have hc := layer_card_le_base_bound t X k P hP
  have hc_real : ((TauAssembly.layer t X k).card : ℝ) ≤ (P : ℝ) + 1 := by
    exact_mod_cast hc
  have hf : (P : ℝ) ≤ C * Real.rpow (X : ℝ) (θ + ε) := by
    exact Nat.floor_le (mul_nonneg (le_of_lt hC) (le_trans (by norm_num) hw))
  calc
    ((TauAssembly.layer t X k).card : ℝ) ≤ (P : ℝ) + 1 := hc_real
    _ ≤ (C + 1) * Real.rpow (X : ℝ) (θ + ε) := by nlinarith

#print axioms layer_card_le_base_bound
#print axioms layer_power_bound_from_base_power_bound

end TauLayerBridge
