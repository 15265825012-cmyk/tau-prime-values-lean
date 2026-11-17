import TauAbcAlgebra
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The square layer must separate the small-p alternative from the branch
where |τ(p)| is provably of the same scale as p^(11/2). -/
namespace TauSquareLower

theorem square_lower_or_small (p l n : ℕ) (X : ℝ)
    (hp : 0 < p) (hX : 0 < X) (hlX : (l : ℝ) ≤ X)
    (habs : ((n ^ 2 : ℤ) - (p ^ 11 : ℤ)).natAbs = l) :
    (p : ℝ) ^ 11 ≤ 2 * X ∨ Real.rpow (p : ℝ) (11 / 2) ≤ 2 * (n : ℝ) := by
  by_cases hsmall : (p : ℝ) ^ 11 ≤ 2 * X
  · exact Or.inl hsmall
  · right
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
    have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdInt : |(n ^ 2 : ℤ) - (p ^ 11 : ℤ)| = (l : ℤ) := by
      rw [← Int.natCast_natAbs, habs]
    have hdReal : |(n : ℝ) ^ 2 - (p : ℝ) ^ 11| = (l : ℝ) := by
      exact_mod_cast hdInt
    have hdLow : -(l : ℝ) ≤ (n : ℝ) ^ 2 - (p : ℝ) ^ 11 :=
      (abs_le.mp hdReal.le).1
    have hpNonneg : 0 ≤ Real.rpow (p : ℝ) (11 / 2) :=
      le_of_lt (Real.rpow_pos_of_pos hpR _)
    have hpow : (Real.rpow (p : ℝ) (11 / 2)) ^ 2 = (p : ℝ) ^ 11 := by
      calc
        _ = Real.rpow (Real.rpow (p : ℝ) (11 / 2)) (2 : ℝ) := by
          exact (Real.rpow_natCast _ 2).symm
        _ = Real.rpow (p : ℝ) ((11 / 2) * 2) := by
          exact (Real.rpow_mul (le_of_lt hpR) _ _).symm
        _ = (p : ℝ) ^ 11 := by
          have he : ((11 / 2 : ℝ) * 2) = (11 : ℝ) := by norm_num
          rw [he]
          exact Real.rpow_natCast (p : ℝ) 11
    nlinarith

end TauSquareLower

#print axioms TauSquareLower.square_lower_or_small
