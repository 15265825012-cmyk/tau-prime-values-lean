import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Elementary identities and divisibility checks for the prime-value problem.
The variables `a` and `p` stand for `τ(p)` and `p`; no implementation of
Ramanujan's tau function or `abc` is assumed in this file.
-/

namespace TauArithmetic

def hecke (a p : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a
  | n + 2 => a * hecke a p (n + 1) - p ^ 11 * hecke a p n

theorem hecke_divisible (a p : ℤ) (h : p ∣ a) (n : ℕ) :
    p ^ n ∣ hecke a p n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hecke]
  | one => simpa [hecke] using h
  | more n hn hn1 =>
      rcases h with ⟨b, hb⟩
      rcases hn with ⟨c, hc⟩
      rcases hn1 with ⟨d, hd⟩
      rw [hecke, hc, hd, hb]
      refine ⟨b * d - p ^ 9 * c, ?_⟩
      simp only [pow_add, pow_one]
      ring

theorem prime_not_divisible_of_hecke_prime
    (a : ℤ) (p ell m : ℕ) (hp : Nat.Prime p) (hell : Nat.Prime ell)
    (hm : 2 ≤ m) (hvalue : (hecke a (p : ℤ) m).natAbs = ell) :
    ¬ (p : ℤ) ∣ a := by
  intro hpa
  have hdiv : ((p ^ m : ℕ) : ℤ) ∣ hecke a (p : ℤ) m := by
    simpa using hecke_divisible a (p : ℤ) hpa m
  have hnat : p ^ m ∣ ell := by
    rw [← hvalue]
    exact Int.natCast_dvd.mp hdiv
  have hmpos : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hpownotone : p ^ m ≠ 1 := Nat.ne_of_gt (Nat.one_lt_pow hmpos hp.one_lt)
  rcases hell.eq_one_or_self_of_dvd (p ^ m) hnat with h | h
  · exact hpownotone h
  · have hprime : Nat.Prime (p ^ m) := h ▸ hell
    exact (Nat.Prime.not_prime_pow hm) hprime

theorem hecke_congruent_power (a p : ℤ) (n : ℕ) :
    p ∣ hecke a p n - a ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hecke]
  | one => simp [hecke]
  | more n hn hn1 =>
      rcases hn1 with ⟨c, hc⟩
      have hrec : hecke a p (n + 1) = p * c + a ^ (n + 1) :=
        sub_eq_iff_eq_add.mp hc
      rw [hecke, hrec]
      refine ⟨a * c - p ^ 10 * hecke a p n, ?_⟩
      simp only [pow_add, pow_one]
      ring

theorem prime_output_ne_base
    (a : ℤ) (p ell m : ℕ) (hp : Nat.Prime p) (hell : Nat.Prime ell)
    (hm : 2 ≤ m) (hvalue : (hecke a (p : ℤ) m).natAbs = ell) :
    ell ≠ p := by
  intro heq
  have hnot := prime_not_divisible_of_hecke_prime a p ell m hp hell hm hvalue
  have hpdiv : p ∣ (hecke a (p : ℤ) m).natAbs := by
    rw [hvalue, heq]
  have hpdivz : (p : ℤ) ∣ hecke a (p : ℤ) m := Int.natCast_dvd.mpr hpdiv
  have hpdivpow : (p : ℤ) ∣ a ^ m := by
    have h := dvd_sub hpdivz (hecke_congruent_power a (p : ℤ) m)
    simpa only [sub_sub_cancel] using h
  have hpdivnat : p ∣ a.natAbs ^ m := by
    have h := Int.natCast_dvd.mp hpdivpow
    simpa only [Int.natAbs_pow] using h
  have hpdiva : p ∣ a.natAbs := hp.dvd_of_dvd_pow hpdivnat
  exact hnot (Int.natCast_dvd.mpr hpdiva)

def squareCoeff (a p : ℤ) : ℤ := a ^ 2 - p ^ 11

def fourthCoeff (a p : ℤ) : ℤ := a ^ 4 - 3 * p ^ 11 * a ^ 2 + p ^ 22

theorem hecke_two (a p : ℤ) : hecke a p 2 = squareCoeff a p := by
  simp only [hecke, squareCoeff]
  ring

theorem hecke_four (a p : ℤ) : hecke a p 4 = fourthCoeff a p := by
  simp only [hecke, fourthCoeff]
  ring

theorem complete_square (a p : ℤ) :
    (2 * a ^ 2 - 3 * p ^ 11) ^ 2 = 5 * p ^ 22 + 4 * fourthCoeff a p := by
  unfold fourthCoeff
  ring

theorem square_dvd_squareCoeff (a p : ℤ) (h : p ∣ a) : p ^ 2 ∣ squareCoeff a p := by
  rcases h with ⟨b, rfl⟩
  unfold squareCoeff
  refine ⟨b ^ 2 - p ^ 9, ?_⟩
  ring

theorem fourth_dvd_fourthCoeff (a p : ℤ) (h : p ∣ a) : p ^ 4 ∣ fourthCoeff a p := by
  rcases h with ⟨b, rfl⟩
  unfold fourthCoeff
  refine ⟨b ^ 4 - 3 * p ^ 9 * b ^ 2 + p ^ 18, ?_⟩
  ring

#print axioms hecke_divisible
#print axioms hecke_two
#print axioms hecke_four
#print axioms prime_not_divisible_of_hecke_prime
#print axioms hecke_congruent_power
#print axioms prime_output_ne_base
#print axioms complete_square
#print axioms square_dvd_squareCoeff
#print axioms fourth_dvd_fourthCoeff

end TauArithmetic
