import TauArithmetic
import TauCoprime
import TauSquareAbc
import TauSquareLower

/-! Bridge an explicit Hecke recurrence to the square-layer abc estimates.
The theorem does not assert that any particular sequence satisfies the recurrence.
-/
namespace TauSquareHecke

theorem square_inputs (a : ℤ) (p l : ℕ)
    (hp : p.Prime) (hl : l.Prime)
    (hvalue : (TauArithmetic.hecke a (p : ℤ) 2).natAbs = l) :
    0 < a.natAbs ∧ Nat.Coprime (p ^ 11) l ∧
      (((a.natAbs ^ 2 : ℕ) : ℤ) - (p ^ 11 : ℤ)).natAbs = l := by
  have hnDiv : ¬ (p : ℤ) ∣ a :=
    TauArithmetic.prime_not_divisible_of_hecke_prime a p l 2 hp hl (by decide) hvalue
  have ha : a ≠ 0 := by
    intro ha0
    apply hnDiv
    rw [ha0]
    exact dvd_zero _
  have hne : l ≠ p :=
    TauArithmetic.prime_output_ne_base a p l 2 hp hl (by decide) hvalue
  have hcop := TauCoprime.pow11_coprime_prime p l hp hl (Ne.symm hne)
  have hcast : ((a.natAbs ^ 2 : ℕ) : ℤ) = a ^ 2 := by
    rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  refine ⟨Int.natAbs_pos.mpr ha, hcop, ?_⟩
  rw [hcast]
  simpa [TauArithmetic.hecke_two, TauArithmetic.squareCoeff] using hvalue

theorem hecke_square_abc_and_branch (habc : TauTarget.abcConjecture)
    (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 < K ∧
      ∀ (a : ℤ) (p l : ℕ) (X : ℝ), p.Prime → l.Prime → 0 < X →
        (l : ℝ) ≤ X → (TauArithmetic.hecke a (p : ℤ) 2).natAbs = l →
        Real.rpow (a.natAbs : ℝ) (1 - δ) ≤ K * Real.rpow ((p : ℝ) * X) (1 + δ) ∧
        ((p : ℝ) ^ 11 ≤ 2 * X ∨
          Real.rpow (p : ℝ) (11 / 2) ≤ 2 * (a.natAbs : ℝ)) := by
  obtain ⟨K, hK, hupper⟩ := TauSquareAbc.square_abc_upper habc δ hδ
  refine ⟨K, hK, ?_⟩
  intro a p l X hp hl hX hlX hvalue
  obtain ⟨ha, hcop, habs⟩ := square_inputs a p l hp hl hvalue
  have hp0 : 0 < p := hp.pos
  have hl0 : 0 < l := hl.pos
  refine ⟨hupper p l a.natAbs X hp0 hl0 ha hX hlX hcop ?_, ?_⟩
  · simpa only [Nat.cast_pow] using habs
  · apply TauSquareLower.square_lower_or_small p l a.natAbs X hp0 hX hlX
    simpa only [Nat.cast_pow] using habs

end TauSquareHecke

#print axioms TauSquareHecke.square_inputs
#print axioms TauSquareHecke.hecke_square_abc_and_branch
