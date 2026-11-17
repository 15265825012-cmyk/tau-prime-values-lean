import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-! Elementary coprimality inputs in the two low prime-power layers. -/

namespace TauCoprime

theorem pow11_coprime_prime (p ℓ : ℕ) (hp : p.Prime) (hℓ : ℓ.Prime)
    (hne : p ≠ ℓ) : Nat.Coprime (p ^ 11) ℓ := by
  exact ((Nat.coprime_primes hp hℓ).2 hne).pow_left 11

theorem gcd_fourth_layer_le_five (p ℓ : ℕ) (hp : p.Prime) (hℓ : ℓ.Prime)
    (hne : p ≠ ℓ) (hodd : Odd p) : Nat.gcd (5 * p ^ 22) (4 * ℓ) ≤ 5 := by
  have hpℓ : Nat.Coprime p ℓ := (Nat.coprime_primes hp hℓ).2 hne
  have hp2 : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hodd
  have hp4 : Nat.Coprime p 4 := by
    simpa using hp2.pow_right 2
  have hp4ℓ : Nat.Coprime p (4 * ℓ) := hp4.mul_right hpℓ
  have hpow : Nat.Coprime (p ^ 22) (4 * ℓ) := hp4ℓ.pow_left 22
  rw [Nat.Coprime.gcd_mul_right_cancel 5 hpow]
  exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 5 (4 * ℓ))

end TauCoprime

#print axioms TauCoprime.pow11_coprime_prime
#print axioms TauCoprime.gcd_fourth_layer_le_five
