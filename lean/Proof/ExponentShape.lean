import ExponentBounds

/-! The odd part of a strict FC counterexample using the Sylow exponent bound. -/
namespace Conjecture55ExponentShape
open Conjecture55Lean4Web Conjecture55Lean4Web

/-- The ordinary Frobenius lower bound already restricts the odd part of a
strict counterexample. For 2-part at least sixteen it is squarefree; for
smaller 2-parts at most one odd prime is repeated, and only to exponent two. -/
theorem odd_part_shape_of_noncyclic_sylow
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ((a = 2 ∨ a = 3) ∧ (∀ p, m.factorization p ≤ 2) ∧
      ∀ p q, 2 ≤ m.factorization p → 2 ≤ m.factorization q → p = q) ∨
    ((a = 4 ∨ a = 5) ∧ Squarefree m) := by
  have hcount := RootWeights.cyclic_count_ge_of_noncyclic_sylow ha hm P hnc hcard hbase
  have ha5 := RootWeights.two_part_le_five_of_noncyclic_sylow ha hm P hnc hcard hbase hlt
  have h2 : ¬2 ∣ m := by
    simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm
  have hω : numPrimeFactors G = m.primeFactors.card + 1 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
    rw [hcard]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 a m Nat.prime_two
      (by omega) hm.pos h2
  have hexp : 2 ^ (numPrimeFactors G + 2) = 8 * 2 ^ m.primeFactors.card := by
    rw [hω, show m.primeFactors.card + 1 + 2 = m.primeFactors.card + 3 by omega,
      pow_add]
    ring
  have hsmall : (a + 2) * m.divisors.card < 8 * 2 ^ m.primeFactors.card := by
    simpa only [hexp] using hcount.trans_lt hlt
  by_cases ha4 : 4 ≤ a
  · right
    refine ⟨by omega, squarefree_of_six_mul_card_divisors_lt m hm.pos ?_⟩
    exact (Nat.mul_le_mul_right _ (by omega : 6 ≤ a + 2)).trans_lt hsmall
  · left
    refine ⟨by omega, factorization_shape_of_four_mul_card_divisors_lt m hm.pos ?_⟩
    exact (Nat.mul_le_mul_right _ (by omega : 4 ≤ a + 2)).trans_lt hsmall

#print axioms odd_part_shape_of_noncyclic_sylow
end Conjecture55ExponentShape
