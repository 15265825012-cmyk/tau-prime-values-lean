import TauTarget
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Radical divisibility bounds for the two low exponent Diophantine equations.
The variables here are arbitrary positive natural numbers, so the conclusions
do not rely on primality or any claim about tau or the abc conjecture. -/

namespace TauRadical

theorem radical_dvd_of_prime_dvd (n m : ℕ) (hm : m ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ m) : TauTarget.radical n ∣ m := by
  unfold TauTarget.radical
  apply (Nat.prod_primeFactors_dvd_iff hm).2
  intro q hq
  have hq' := Nat.mem_primeFactors.mp hq
  exact Nat.mem_primeFactors.mpr ⟨hq'.1, h q hq'.1 hq'.2.1, hm⟩

theorem radical_square_layer (p l a : ℕ) (hp : 0 < p) (hl : 0 < l) (ha : 0 < a) :
    TauTarget.radical (p ^ 11 * l * a ^ 2) ≤ p * l * a := by
  have hpos : 0 < p * l * a := by positivity
  apply Nat.le_of_dvd hpos
  apply radical_dvd_of_prime_dvd _ _ (Nat.ne_of_gt hpos)
  intro q hq hdvd
  simp only [hq.dvd_mul] at hdvd ⊢
  rcases hdvd with ((hp11 | hl') | ha2)
  · exact Or.inl (Or.inl (hq.dvd_of_dvd_pow hp11))
  · exact Or.inl (Or.inr hl')
  · exact Or.inr (hq.dvd_of_dvd_pow ha2)

theorem radical_fourth_layer (p l u : ℕ) (hp : 0 < p) (hl : 0 < l) (hu : 0 < u) :
    TauTarget.radical (5 * p ^ 22 * 4 * l * u ^ 2) ≤ 10 * p * l * u := by
  have hpos : 0 < 10 * p * l * u := by positivity
  apply Nat.le_of_dvd hpos
  apply radical_dvd_of_prime_dvd _ _ (Nat.ne_of_gt hpos)
  intro q hq hdvd
  change q ∣ 5 * 2 * p * l * u
  simp only [hq.dvd_mul] at hdvd ⊢
  rcases hdvd with ((((h5 | hp22) | h4) | hl') | hu2)
  · exact Or.inl (Or.inl (Or.inl (Or.inl h5)))
  · exact Or.inl (Or.inl (Or.inr (hq.dvd_of_dvd_pow hp22)))
  · have h2 : q ∣ (2 : ℕ) := by
      apply hq.dvd_of_dvd_pow (n := 2)
      norm_num at h4 ⊢
      exact h4
    exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
  · exact Or.inl (Or.inr hl')
  · exact Or.inr (hq.dvd_of_dvd_pow hu2)

end TauRadical

#print axioms TauRadical.radical_dvd_of_prime_dvd
#print axioms TauRadical.radical_square_layer
#print axioms TauRadical.radical_fourth_layer
