import TauTarget
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Work towards the signed form of the explicitly assumed positive abc input. -/

namespace TauSignedAbc

theorem natAbs_eq_if (a : ℤ) : (a.natAbs : ℤ) = if 0 ≤ a then a else -a := by
  rw [Int.natCast_natAbs]
  split_ifs with ha
  · exact abs_of_nonneg ha
  · exact abs_of_neg (by omega)

theorem natAbs_add_trichotomy (a b c : ℤ) (h : a + b = c) :
    a.natAbs + b.natAbs = c.natAbs ∨
      a.natAbs + c.natAbs = b.natAbs ∨
      b.natAbs + c.natAbs = a.natAbs := by
  have ha := natAbs_eq_if a
  have hb := natAbs_eq_if b
  have hc := natAbs_eq_if c
  split_ifs at ha hb hc <;> omega

/-- The positive-integer abc hypothesis implies the signed-integer form.
The constant depends on δ but is uniform in the integer triple. -/
theorem signed_abc_of_positive_abc (habc : TauTarget.abcConjecture)
    (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
        Nat.Coprime a.natAbs b.natAbs → a + b = c →
        (c.natAbs : ℝ) ≤ K * Real.rpow (TauTarget.radical (a * b * c).natAbs : ℝ) (1 + δ) := by
  obtain ⟨K, hK, hbound⟩ := habc δ hδ
  refine ⟨K, hK, ?_⟩
  intro a b c ha hb hcop hsum
  by_cases hc : c = 0
  · have hz : c.natAbs = 0 := by simp [hc]
    rw [hz, Nat.cast_zero]
    exact mul_nonneg (le_of_lt hK) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have ha_pos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
    have hb_pos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
    have hc_pos : 0 < c.natAbs := Int.natAbs_pos.mpr hc
    rcases natAbs_add_trichotomy a b c hsum with hab | hac | hbc
    · have h := hbound a.natAbs b.natAbs c.natAbs ha_pos hb_pos hcop hab
      simpa only [Int.natAbs_mul] using h
    · have hacop' : Nat.Coprime a.natAbs (a.natAbs + c.natAbs) := by
        rw [hac]
        exact hcop
      have hacop : Nat.Coprime a.natAbs c.natAbs :=
        Nat.coprime_self_add_right.mp hacop'
      have h := hbound a.natAbs c.natAbs b.natAbs ha_pos hc_pos hacop hac
      have hc_le : c.natAbs ≤ b.natAbs := by omega
      have hle : (c.natAbs : ℝ) ≤ (b.natAbs : ℝ) := Nat.cast_le.mpr hc_le
      apply le_trans hle
      simpa only [Int.natAbs_mul, mul_comm, mul_left_comm, mul_assoc] using h
    · have hbcop' : Nat.Coprime b.natAbs (b.natAbs + c.natAbs) := by
        rw [hbc]
        exact hcop.symm
      have hbcop : Nat.Coprime b.natAbs c.natAbs :=
        Nat.coprime_self_add_right.mp hbcop'
      have h := hbound b.natAbs c.natAbs a.natAbs hb_pos hc_pos hbcop hbc
      have hc_le : c.natAbs ≤ a.natAbs := by omega
      have hle : (c.natAbs : ℝ) ≤ (a.natAbs : ℝ) := Nat.cast_le.mpr hc_le
      apply le_trans hle
      simpa only [Int.natAbs_mul, mul_comm, mul_left_comm, mul_assoc] using h

end TauSignedAbc

#print axioms TauSignedAbc.natAbs_add_trichotomy
#print axioms TauSignedAbc.signed_abc_of_positive_abc
