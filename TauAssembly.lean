import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factorization.Basic
import Lean.Elab.Tactic.Omega

/-!
Finite bookkeeping for prime absolute values of an integer-valued sequence.
The theorem below is conditional on the prime-power reduction `hred`; it does
not establish that reduction for the Ramanujan tau function.
-/

namespace TauAssembly

noncomputable def primeValues (t : ℕ → ℤ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun ℓ => ℓ.Prime ∧ ∃ n, (t n).natAbs = ℓ)

noncomputable def layer (t : ℕ → ℤ) (X k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter
    (fun ℓ => ℓ.Prime ∧ ∃ p, p.Prime ∧ (t (p ^ (2 * k))).natAbs = ℓ)

noncomputable def highLayers (t : ℕ → ℤ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter
    (fun ℓ => ℓ.Prime ∧ ∃ p k, p.Prime ∧ 3 ≤ k ∧ (t (p ^ (2 * k))).natAbs = ℓ)

theorem partition_subset (t : ℕ → ℤ) (X : ℕ)
    (hred : ∀ n, (t n).natAbs.Prime → (t n).natAbs ≠ 2 →
      ∃ p k, p.Prime ∧ 1 ≤ k ∧ n = p ^ (2 * k)) :
    primeValues t X ⊆ {2} ∪ layer t X 1 ∪ layer t X 2 ∪ highLayers t X := by
  classical
  intro ℓ hℓ
  simp only [primeValues, Finset.mem_filter, Finset.mem_range] at hℓ
  rcases hℓ with ⟨hrange, hprime, n, hn⟩
  by_cases h2 : ℓ = 2
  · simp [h2]
  have habsprime : (t n).natAbs.Prime := by simpa [hn] using hprime
  have hne : (t n).natAbs ≠ 2 := by simpa [hn] using h2
  rcases hred n habsprime hne with ⟨p, k, hp, hk, hnform⟩
  have hvalue : (t (p ^ (2 * k))).natAbs = ℓ := by simpa [hnform] using hn
  rcases lt_or_ge k 3 with hsmall | hlarge
  · have cases : k = 1 ∨ k = 2 := by omega
    rcases cases with rfl | rfl
    · simp only [Finset.mem_union, Finset.mem_singleton, layer, Finset.mem_filter,
        Finset.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨hrange, hprime, p, hp, hvalue⟩))
    · simp only [Finset.mem_union, Finset.mem_singleton, layer, Finset.mem_filter,
        Finset.mem_range]
      exact Or.inl (Or.inr ⟨hrange, hprime, p, hp, hvalue⟩)
  · simp only [Finset.mem_union, highLayers, Finset.mem_filter, Finset.mem_range]
    exact Or.inr ⟨hrange, hprime, p, k, hp, hlarge, hvalue⟩

theorem partition_card (t : ℕ → ℤ) (X : ℕ)
    (hred : ∀ n, (t n).natAbs.Prime → (t n).natAbs ≠ 2 →
      ∃ p k, p.Prime ∧ 1 ≤ k ∧ n = p ^ (2 * k)) :
    (primeValues t X).card ≤
      1 + (layer t X 1).card + (layer t X 2).card + (highLayers t X).card := by
  classical
  have h := Finset.card_le_card (partition_subset t X hred)
  have h₁ := Finset.card_union_le ({2} : Finset ℕ) (layer t X 1)
  have h₂ := Finset.card_union_le ({2} ∪ layer t X 1) (layer t X 2)
  have h₃ := Finset.card_union_le ({2} ∪ layer t X 1 ∪ layer t X 2) (highLayers t X)
  simp only [Finset.card_singleton] at h₁
  omega

/-- Pointwise assembly. The three bounds are independent inputs for the
    square, fourth-power and high-power layers, respectively. No analytic
    estimate is asserted or discharged by this bookkeeping theorem. -/
theorem combine_layer_bounds (t : ℕ → ℤ) (X B1 B2 B3 : ℕ)
    (hred : ∀ n, (t n).natAbs.Prime → (t n).natAbs ≠ 2 →
      ∃ p k, p.Prime ∧ 1 ≤ k ∧ n = p ^ (2 * k))
    (h1 : (layer t X 1).card ≤ B1)
    (h2 : (layer t X 2).card ≤ B2)
    (h3 : (highLayers t X).card ≤ B3) :
    (primeValues t X).card ≤ 1 + B1 + B2 + B3 := by
  have h := partition_card t X hred
  omega

/-- Multiplicativity and non-unit coefficients force a prime value to come
    from a prime-power input. These hypotheses are explicit: this lemma does
    not prove them for the Ramanujan tau function. -/
theorem prime_power_of_prime_value (t : ℕ → ℤ)
    (ht0 : (t 0).natAbs = 0) (ht1 : (t 1).natAbs = 1)
    (hnonunit : ∀ n, 1 < n → (t n).natAbs ≠ 1)
    (hmul : ∀ a b, Nat.Coprime a b → t (a * b) = t a * t b) :
    ∀ n, (t n).natAbs.Prime → ∃ p e, p.Prime ∧ 0 < e ∧ n = p ^ e := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he _
    exact ⟨p, e, hp, he, rfl⟩
  · intro hprime
    rw [ht0] at hprime
    exact (Nat.not_prime_zero hprime).elim
  · intro hprime
    rw [ht1] at hprime
    exact (Nat.not_prime_one hprime).elim
  · intro a b ha hb hab _ _ hprime
    have hprod : ((t a).natAbs * (t b).natAbs).Prime := by
      simpa [hmul a b hab, Int.natAbs_mul] using hprime
    rcases Nat.prime_mul_iff.mp hprod with hleft | hright
    · exact False.elim (hnonunit b hb hleft.2)
    · exact False.elim (hnonunit a ha hright.2)

/-- The square in the parity hypothesis forces the exponent of the prime
    power to be even; the primality of the value supplies its oddness. -/
theorem odd_prime_power_reduction (t : ℕ → ℤ)
    (ht0 : (t 0).natAbs = 0) (ht1 : (t 1).natAbs = 1)
    (hnonunit : ∀ n, 1 < n → (t n).natAbs ≠ 1)
    (hmul : ∀ a b, Nat.Coprime a b → t (a * b) = t a * t b)
    (hparity : ∀ n, Odd (t n).natAbs ↔ Odd n ∧ ∃ m, n = m ^ 2) :
    ∀ n, (t n).natAbs.Prime → (t n).natAbs ≠ 2 →
      ∃ p k, p.Prime ∧ 1 ≤ k ∧ n = p ^ (2 * k) := by
  intro n hprime hne
  have hodd : Odd (t n).natAbs := hprime.odd_of_ne_two hne
  obtain ⟨_hnodd, m, hm⟩ := (hparity n).mp hodd
  obtain ⟨p, e, hp, he, hn⟩ := prime_power_of_prime_value t ht0 ht1 hnonunit hmul n hprime
  have heq : (p ^ e).factorization p = (m ^ 2).factorization p :=
    congrArg (fun z : ℕ => z.factorization p) (hn.symm.trans hm)
  have heven : e = 2 * m.factorization p := by
    rw [Nat.factorization_pow_self hp, Nat.factorization_pow] at heq
    simpa [Finsupp.smul_apply, nsmul_eq_mul] using heq
  refine ⟨p, m.factorization p, hp, ?_, ?_⟩
  · omega
  · simpa [heven] using hn

/-- Complete finite bookkeeping from standard arithmetic hypotheses and
    three separate pointwise layer bounds. -/
theorem combine_from_arithmetic_hypotheses (t : ℕ → ℤ) (X B1 B2 B3 : ℕ)
    (ht0 : (t 0).natAbs = 0) (ht1 : (t 1).natAbs = 1)
    (hnonunit : ∀ n, 1 < n → (t n).natAbs ≠ 1)
    (hmul : ∀ a b, Nat.Coprime a b → t (a * b) = t a * t b)
    (hparity : ∀ n, Odd (t n).natAbs ↔ Odd n ∧ ∃ m, n = m ^ 2)
    (h1 : (layer t X 1).card ≤ B1)
    (h2 : (layer t X 2).card ≤ B2)
    (h3 : (highLayers t X).card ≤ B3) :
    (primeValues t X).card ≤ 1 + B1 + B2 + B3 := by
  exact combine_layer_bounds t X B1 B2 B3
    (odd_prime_power_reduction t ht0 ht1 hnonunit hmul hparity) h1 h2 h3

end TauAssembly

#print axioms TauAssembly.partition_subset
#print axioms TauAssembly.partition_card
#print axioms TauAssembly.combine_layer_bounds
#print axioms TauAssembly.prime_power_of_prime_value
#print axioms TauAssembly.odd_prime_power_reduction
#print axioms TauAssembly.combine_from_arithmetic_hypotheses
