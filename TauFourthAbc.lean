import TauSignedAbc
import TauRadical
import TauArithmetic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! Coprimality in the fourth-power layer after isolating the single value 5. -/

namespace TauFourthAbc

theorem coprime_fourth_except_five (p l : ℕ) (hp : p.Prime) (hl : l.Prime)
    (hne : p ≠ l) (hodd : Odd p) (hl5 : l ≠ 5) :
    Nat.Coprime (5 * p ^ 22) (4 * l) := by
  have hp_l : Nat.Coprime p l := (Nat.coprime_primes hp hl).2 hne
  have hp2 : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hodd
  have hp4 : Nat.Coprime p 4 := by simpa using hp2.pow_right 2
  have hpow : Nat.Coprime (p ^ 22) (4 * l) := (hp4.mul_right hp_l).pow_left 22
  have h5l : Nat.Coprime 5 l := (Nat.coprime_primes (by norm_num) hl).2 (Ne.symm hl5)
  have h5four : Nat.Coprime 5 4 := by norm_num
  exact (h5four.mul_right h5l).mul_left hpow

/-- The abc application for the fourth-power equation; the sole exceptional
prime value 5 is omitted.  The equation and positivity of u are inputs. -/
theorem abc_fourth_square_bound (habc : TauTarget.abcConjecture)
    (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 < K ∧
    ∀ (p l u : ℕ) (s : ℤ), p.Prime → l.Prime → p ≠ l → Odd p → l ≠ 5 →
      0 < u → s.natAbs = 4 * l →
      (5 * (p : ℤ)^22) + s = (u : ℤ)^2 →
      (u : ℝ)^2 ≤ K * Real.rpow ((10 * p * l * u : ℕ) : ℝ) (1 + δ) := by
  obtain ⟨K, hK, habcbound⟩ := TauSignedAbc.signed_abc_of_positive_abc habc δ hδ
  refine ⟨K, hK, ?_⟩
  intro p l u s hp hl hne hodd hl5 hu hs heq
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have ha : (5 * (p : ℤ)^22) ≠ 0 := by positivity
  have hb : s ≠ 0 := by
    have hpos : 0 < s.natAbs := by rw [hs]; have := hl.pos; positivity
    exact Int.natAbs_pos.mp hpos
  have hc : Nat.Coprime (5 * (p : ℤ)^22).natAbs s.natAbs := by
    simpa [Int.natAbs_mul, hs] using coprime_fourth_except_five p l hp hl hne hodd hl5
  have h := habcbound (5 * (p : ℤ)^22) s ((u : ℤ)^2) ha hb hc heq
  have hrad : TauTarget.radical ((5 * (p : ℤ)^22 * s * (u : ℤ)^2).natAbs)
      ≤ 10 * p * l * u := by
    simpa [Int.natAbs_mul, hs, mul_assoc] using TauRadical.radical_fourth_layer p l u hp.pos hl.pos hu
  have hradreal : (TauTarget.radical ((5 * (p : ℤ)^22 * s * (u : ℤ)^2).natAbs) : ℝ)
      ≤ ((10 * p * l * u : ℕ) : ℝ) := Nat.cast_le.mpr hrad
  have hpow := Real.rpow_le_rpow (by positivity) hradreal (by linarith : 0 ≤ 1 + δ)
  have hfin := le_trans h (mul_le_mul_of_nonneg_left hpow (le_of_lt hK))
  simpa using hfin

/-- Specialization to an integer Hecke recurrence.  The relation between this
recurrence and the concrete Ramanujan tau sequence is not assumed silently. -/
theorem abc_hecke_fourth_bound (habc : TauTarget.abcConjecture)
    (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 < K ∧
    ∀ (p l : ℕ) (a : ℤ), p.Prime → l.Prime → Odd p → l ≠ 5 →
      (TauArithmetic.hecke a p 4).natAbs = l →
      let u : ℕ := (2 * a^2 - 3 * (p : ℤ)^11).natAbs
      (u : ℝ)^2 ≤ K * Real.rpow ((10 * p * l * u : ℕ) : ℝ) (1 + δ) := by
  obtain ⟨K, hK, hbound⟩ := abc_fourth_square_bound habc δ hδ
  refine ⟨K, hK, ?_⟩
  intro p l a hp hl hodd hl5 hv
  have hne : p ≠ l := by
    exact Ne.symm (TauArithmetic.prime_output_ne_base a p l 4 hp hl (by norm_num) hv)
  let u : ℕ := (2 * a^2 - 3 * (p : ℤ)^11).natAbs
  have hodd11 : Odd ((p : ℤ)^11) := by
    exact_mod_cast (show Odd (p ^ 11) from hodd.pow)
  have hune : 2 * a^2 - 3 * (p : ℤ)^11 ≠ 0 := by
    rcases hodd11 with ⟨k, hk⟩
    intro h
    omega
  have hu : 0 < u := Int.natAbs_pos.mpr hune
  have hs : (4 * TauArithmetic.hecke a p 4).natAbs = 4 * l := by
    simp [Int.natAbs_mul, hv]
  have hsq : ((u : ℤ)^2) = (2 * a^2 - 3 * (p : ℤ)^11)^2 := by
    simp [u, Int.natCast_natAbs, sq_abs]
  have heq : 5 * (p : ℤ)^22 + 4 * TauArithmetic.hecke a p 4 = (u : ℤ)^2 := by
    rw [hsq, TauArithmetic.hecke_four]
    exact (TauArithmetic.complete_square a p).symm
  exact hbound p l u (4 * TauArithmetic.hecke a p 4) hp hl hne hodd hl5 hu hs heq

end TauFourthAbc

#print axioms TauFourthAbc.coprime_fourth_except_five
#print axioms TauFourthAbc.abc_fourth_square_bound
#print axioms TauFourthAbc.abc_hecke_fourth_bound
