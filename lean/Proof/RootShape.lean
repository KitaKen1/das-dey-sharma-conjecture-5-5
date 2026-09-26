import Conjecture55Foundation

/-! Actual divisor-count bounds imply the small order shape and the FC threshold. -/

namespace Conjecture55RootShape
open Conjecture55Lean4Web

/-- An actual divisor-count lower bound, without a comparison bijection,
forces the same small-order shape under the strict FC bound. -/
theorem order_shape_of_divisor_count_lower_bound
    {G : Type*} [Group G] [Fintype G]
    (a m : ℕ) (ha : 2 ≤ a) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ a * m)
    (hcount : 2 * a * m.divisors.card ≤ cyc G)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    (a = 2 ∧ (∀ p, m.factorization p ≤ 2) ∧
      ∀ p q, 2 ≤ m.factorization p → 2 ≤ m.factorization q → p = q) ∨
    (a = 3 ∧ Squarefree m) := by
  have ha1 : 1 ≤ a := by omega
  have hmpos : 0 < m := hm.pos
  have h2 : ¬ 2 ∣ m := by
    simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm
  have hω : numPrimeFactors G = m.primeFactors.card + 1 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
    rw [hcard]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 a m Nat.prime_two ha1 hmpos h2
  have hsmall : 2 * a * m.divisors.card < 2 ^ (numPrimeFactors G + 2) :=
    hcount.trans_lt hlt
  have ht : 1 ≤ numPrimeFactors G := by omega
  have hd : 2 ^ (numPrimeFactors G - 1) ≤ m.divisors.card := by
    rw [hω]
    simpa using two_pow_card_primeFactors_le_card_divisors m hmpos
  have hcases := two_part_exponent_restriction a m.divisors.card (numPrimeFactors G)
    ha ht hd hsmall
  have hsmall' : 2 * a * m.divisors.card < 8 * 2 ^ m.primeFactors.card := by
    have hexp : 2 ^ (numPrimeFactors G + 2) = 8 * 2 ^ m.primeFactors.card := by
      rw [hω, show m.primeFactors.card + 1 + 2 = m.primeFactors.card + 3 by omega,
        pow_add]
      ring
    rwa [hexp] at hsmall
  rcases hcases with hA | hA
  · left
    refine ⟨hA, ?_⟩
    apply factorization_shape_of_four_mul_card_divisors_lt m hmpos
    simpa [hA] using hsmall'
  · right
    refine ⟨hA, ?_⟩
    apply squarefree_of_six_mul_card_divisors_lt m hmpos
    simpa [hA] using hsmall'

/-- The divisor-count bound `8 τ(m)` already reaches the exact FC threshold.
The conclusion holds for every positive two-part exponent, in particular `a ≥ 3`. -/
theorem threshold_le_of_eight_mul_divisor_count
    {G : Type*} [Group G] [Fintype G]
    (a m : ℕ) (ha : 1 ≤ a) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ a * m)
    (hcount : 8 * m.divisors.card ≤ cyc G) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  have h2 : ¬ 2 ∣ m := by
    simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm
  have hω : numPrimeFactors G = m.primeFactors.card + 1 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
    rw [hcard]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 a m Nat.prime_two ha hm.pos h2
  have hexp : 2 ^ (numPrimeFactors G + 2) = 8 * 2 ^ m.primeFactors.card := by
    rw [hω, show m.primeFactors.card + 1 + 2 = m.primeFactors.card + 3 by omega,
      pow_add]
    ring
  rw [hexp]
  exact (Nat.mul_le_mul_left 8 (two_pow_card_primeFactors_le_card_divisors m hm.pos)).trans
    hcount

#print axioms order_shape_of_divisor_count_lower_bound
#print axioms threshold_le_of_eight_mul_divisor_count

end Conjecture55RootShape
