import TauSignedAbc
import TauRadical
import TauAbcAlgebra

/-!
Apply the explicitly assumed abc conjecture to the square-layer equation.
No arithmetic properties of tau are postulated here.
-/
namespace TauSquareAbc

theorem square_abc_core (habc : TauTarget.abcConjecture)
    (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 < K ∧
      ∀ p l n : ℕ, 0 < p → 0 < l → 0 < n →
        Nat.Coprime (p ^ 11) l →
        ((n ^ 2 : ℤ) - (p ^ 11 : ℤ)).natAbs = l →
        (n : ℝ) ^ 2 ≤ K * Real.rpow ((p * l * n : ℕ) : ℝ) (1 + δ) := by
  obtain ⟨K, hK, hbound⟩ := TauSignedAbc.signed_abc_of_positive_abc habc δ hδ
  refine ⟨K, hK, ?_⟩
  intro p l n hp hl hn hcop habs
  let A : ℤ := (p ^ 11 : ℤ)
  let B : ℤ := (n ^ 2 : ℤ) - (p ^ 11 : ℤ)
  let C : ℤ := (n ^ 2 : ℤ)
  have hAabs : A.natAbs = p ^ 11 := by simp [A]
  have hBabs : B.natAbs = l := habs
  have hCabs : C.natAbs = n ^ 2 := by simp [C]
  have hA : A ≠ 0 := by
    intro hz
    have := hAabs
    rw [hz] at this
    simp at this
    have hpowne : p ^ 11 ≠ 0 := pow_ne_zero _ (Nat.ne_of_gt hp)
    exact hpowne this.symm
  have hB : B ≠ 0 := by
    intro hz
    rw [hz] at hBabs
    simp at hBabs
    omega
  have hsum : A + B = C := by dsimp [A, B, C]; ring
  have hcop' : Nat.Coprime A.natAbs B.natAbs := by simpa [hAabs, hBabs] using hcop
  have hraw := hbound A B C hA hB hcop' hsum
  have hprod : (A * B * C).natAbs = p ^ 11 * l * n ^ 2 := by
    simp [Int.natAbs_mul, hAabs, hBabs, hCabs]
  rw [hprod, hCabs] at hraw
  have hrad := TauRadical.radical_square_layer p l n hp hl hn
  have hrad' : (TauTarget.radical (p ^ 11 * l * n ^ 2) : ℝ) ≤ (p * l * n : ℕ) :=
    Nat.cast_le.mpr hrad
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hrad' (by linarith : 0 ≤ 1 + δ)
  have hh := mul_le_mul_of_nonneg_left hpow (le_of_lt hK)
  have hraw' := le_trans hraw hh
  rw [Nat.cast_pow] at hraw'
  exact hraw'

theorem square_abc_upper (habc : TauTarget.abcConjecture)
    (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 < K ∧
      ∀ p l n : ℕ, ∀ X : ℝ, 0 < p → 0 < l → 0 < n → 0 < X →
        (l : ℝ) ≤ X → Nat.Coprime (p ^ 11) l →
        ((n ^ 2 : ℤ) - (p ^ 11 : ℤ)).natAbs = l →
        Real.rpow (n : ℝ) (1 - δ) ≤ K * Real.rpow ((p : ℝ) * X) (1 + δ) := by
  obtain ⟨K, hK, hcore⟩ := square_abc_core habc δ hδ
  refine ⟨K, hK, ?_⟩
  intro p l n X hp hl hn hX hlX hcop habs
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have hcore' := hcore p l n hp hl hn hcop habs
  have hprod : (p : ℝ) * (l : ℝ) ≤ (p : ℝ) * X :=
    mul_le_mul_of_nonneg_left hlX (le_of_lt hpR)
  have hpow : Real.rpow ((p : ℝ) * (l : ℝ)) (1 + δ) ≤
      Real.rpow ((p : ℝ) * X) (1 + δ) :=
    Real.rpow_le_rpow (by positivity) hprod (by linarith)
  have hmain : Real.rpow (n : ℝ) (1 - δ) * Real.rpow (n : ℝ) (1 + δ) ≤
      (K * Real.rpow ((p : ℝ) * X) (1 + δ)) * Real.rpow (n : ℝ) (1 + δ) := by
    calc
      _ = Real.rpow (n : ℝ) ((1 - δ) + (1 + δ)) := (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ 2 := by
        have h : (1 - δ) + (1 + δ) = (2 : ℝ) := by ring
        rw [h]
        exact Real.rpow_natCast (n : ℝ) 2
      _ ≤ K * Real.rpow ((p * l * n : ℕ) : ℝ) (1 + δ) := hcore'
      _ = (K * Real.rpow ((p : ℝ) * (l : ℝ)) (1 + δ)) * Real.rpow (n : ℝ) (1 + δ) := by
        push_cast
        have hh : Real.rpow (((p : ℝ) * (l : ℝ)) * (n : ℝ)) (1 + δ) =
            Real.rpow ((p : ℝ) * (l : ℝ)) (1 + δ) * Real.rpow (n : ℝ) (1 + δ) :=
          Real.mul_rpow (by positivity) (le_of_lt hnR)
        rw [hh]
        ring
      _ ≤ (K * Real.rpow ((p : ℝ) * X) (1 + δ)) * Real.rpow (n : ℝ) (1 + δ) := by
        have hnP : 0 ≤ Real.rpow (n : ℝ) (1 + δ) :=
          le_of_lt (Real.rpow_pos_of_pos hnR _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (le_of_lt hK)) hnP
  exact le_of_mul_le_mul_right hmain (Real.rpow_pos_of_pos hnR _)

end TauSquareAbc

#print axioms TauSquareAbc.square_abc_core
#print axioms TauSquareAbc.square_abc_upper
