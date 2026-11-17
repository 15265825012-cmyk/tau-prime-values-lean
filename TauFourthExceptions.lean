import TauAssembly
import Mathlib.Tactic

namespace TauFourthExceptions

/-- In bounding fourth-power values, the base 2 and the value 5 contribute
at most one output each, irrespective of whether those values are prime. -/
theorem layer_card_le_with_two_exceptions (t : ℕ → ℤ) (X P : ℕ)
    (hbound : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ((t (p ^ 4)).natAbs).Prime → (t (p ^ 4)).natAbs ≠ 5 →
      (t (p ^ 4)).natAbs ≤ X → p ≤ P) :
    (TauAssembly.layer t X 2).card ≤ P + 3 := by
  classical
  let ex : Finset ℕ := {5, (t (2^4)).natAbs}
  let values := (Finset.range (P + 1)).image (fun p => (t (p^4)).natAbs)
  have hsub : TauAssembly.layer t X 2 ⊆ ex ∪ values := by
    intro ell hell
    simp only [TauAssembly.layer, Finset.mem_filter, Finset.mem_range] at hell
    obtain ⟨hell_lt, hell_prime, p, hp, hpval⟩ := hell
    have hval : (t (p^4)).natAbs = ell := by simpa using hpval
    by_cases h5 : ell = 5
    · simp [h5, ex]
    by_cases hp2 : p = 2
    · have hval2 : (t (2^4)).natAbs = ell := by simpa [hp2] using hval
      simp [ex, ← hval2]
    have hprime : ((t (p^4)).natAbs).Prime := by simpa [hval] using hell_prime
    have hne5 : (t (p^4)).natAbs ≠ 5 := by simpa [hval] using h5
    have hle : (t (p^4)).natAbs ≤ X := by rw [hval]; omega
    have hp_le := hbound p hp hp2 hprime hne5 hle
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨p, Finset.mem_range.mpr (by omega), hval⟩
  have hex : ex.card ≤ 2 := Finset.card_le_two
  have hv : values.card ≤ P + 1 := by
    exact le_trans Finset.card_image_le (by simp)
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le ex values
  omega

theorem layer_power_bound_from_nonexceptional_bases
    (t : ℕ → ℤ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hbase : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ X : ℕ, N ≤ X → ∀ p : ℕ, p.Prime → p ≠ 2 →
        ((t (p^4)).natAbs).Prime → (t (p^4)).natAbs ≠ 5 →
        (t (p^4)).natAbs ≤ X →
        (p : ℝ) ≤ C * Real.rpow (X : ℝ) (θ + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ X : ℕ, N ≤ X →
        ((TauAssembly.layer t X 2).card : ℝ) ≤
          C * Real.rpow (X : ℝ) (θ + ε) := by
  intro ε hε
  obtain ⟨C, hC, N, hN⟩ := hbase ε hε
  refine ⟨C + 3, by linarith, N + 1, ?_⟩
  intro X hX
  have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hw : 1 ≤ Real.rpow (X : ℝ) (θ + ε) :=
    Real.one_le_rpow hx1 (by linarith)
  let P : ℕ := ⌊C * Real.rpow (X : ℝ) (θ + ε)⌋₊
  have hP : ∀ p : ℕ, p.Prime → p ≠ 2 → ((t (p^4)).natAbs).Prime →
      (t (p^4)).natAbs ≠ 5 → (t (p^4)).natAbs ≤ X → p ≤ P := by
    intro p hp hp2 hprime h5 hle
    exact Nat.le_floor (hN X (by omega) p hp hp2 hprime h5 hle)
  have hc := layer_card_le_with_two_exceptions t X P hP
  have hc_real : ((TauAssembly.layer t X 2).card : ℝ) ≤ (P : ℝ) + 3 := by
    exact_mod_cast hc
  have hf : (P : ℝ) ≤ C * Real.rpow (X : ℝ) (θ + ε) := by
    exact Nat.floor_le (mul_nonneg (le_of_lt hC) (le_trans (by norm_num) hw))
  calc
    ((TauAssembly.layer t X 2).card : ℝ) ≤ (P : ℝ) + 3 := hc_real
    _ ≤ (C + 3) * Real.rpow (X : ℝ) (θ + ε) := by nlinarith

end TauFourthExceptions

#print axioms TauFourthExceptions.layer_card_le_with_two_exceptions
#print axioms TauFourthExceptions.layer_power_bound_from_nonexceptional_bases
