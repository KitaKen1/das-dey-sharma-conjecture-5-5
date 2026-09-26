import Conjecture55Foundation
import PSL2CyclicCount

/-!
# The prime-field PSL₂ case using the copied FC definitions

This theorem is independent of the unfinished general conjecture. The `Fintype`
instance is arbitrary. The shared PSL₂ package must be available to the project.
-/

namespace Conjecture55Lean4Web

/-- The FC cyclic-subgroup threshold holds for PSL₂ over every prime field
of order at least five, for any enumeration of its elements. -/
theorem psl2_threshold_le_cyc {p : ℕ} [Fact p.Prime]
    [Fintype (Conjecture55PSL2.PSL2 p)] (hp : 5 ≤ p) :
    2 ^ (numPrimeFactors (Conjecture55PSL2.PSL2 p) + 2) ≤
      cyc (Conjecture55PSL2.PSL2 p) := by
  simpa only [numPrimeFactors, cyc, ← Nat.card_eq_fintype_card] using
    Conjecture55PSL2.psl2_fc_threshold_le_cyclic_count hp

#print axioms psl2_threshold_le_cyc

end Conjecture55Lean4Web

namespace Conjecture55Lean4Web.PSL2Extensions

open Conjecture55PSL2

/-- Enlarging an even-order subgroup by a power-of-two index introduces
no new prime divisors of the group order. -/
theorem primeFactors_eq_of_index_pow_two
    {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    (h2 : 2 ∣ Nat.card S) (k : ℕ) (hindex : S.index = 2 ^ k) :
    (Nat.card G).primeFactors = (Nat.card S).primeFactors := by
  classical
  rw [← S.index_mul_card, hindex]
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.primeFactors_mul (by positivity) Nat.card_pos.ne',
      Nat.primeFactors_pow_succ, Nat.prime_two.primeFactors]
    apply Finset.union_eq_right.mpr
    apply Finset.singleton_subset_iff.mpr
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, Nat.card_pos.ne'⟩

/-- PSL₂ over a prime field of order at least five has even order. -/
theorem two_dvd_card_psl2 {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    2 ∣ Nat.card (PSL2 p) := by
  have hmod := Conjecture55Arithmetic.prime_sq_mod_twentyfour p Fact.out hp
  have h4 : 4 ∣ p ^ 2 - 1 := by omega
  obtain ⟨k, hk⟩ := h4
  refine ⟨p * k, ?_⟩
  have hcard := card_psl2_mul_two hp
  rw [hk] at hcard
  nlinarith

/-- Any finite group containing PSL₂(p) with power-of-two index meets
the cyclic-subgroup threshold, without a prime-factor equality assumption. -/
theorem threshold_le_of_psl2_subgroup_index_pow_two
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (S : Subgroup G) (e : PSL2 p ≃* S)
    (k : ℕ) (hindex : S.index = 2 ^ k) :
    2 ^ ((Nat.card G).primeFactors.card + 2) ≤ cyc G := by
  have hcard : Nat.card (PSL2 p) = Nat.card S := Nat.card_congr e.toEquiv
  have h2 : 2 ∣ Nat.card S := hcard ▸ two_dvd_card_psl2 hp
  have hprimes : (Nat.card G).primeFactors = (Nat.card (PSL2 p)).primeFactors := by
    rw [primeFactors_eq_of_index_pow_two S h2 k hindex, ← hcard]
  rw [hprimes]
  calc
    2 ^ ((Nat.card (PSL2 p)).primeFactors.card + 2) ≤ cyc (PSL2 p) :=
      psl2_fc_threshold_le_cyclic_count hp
    _ = cyc S := Conjecture55Lean4Web.cyc_eq_of_mulEquiv e
    _ ≤ cyc G := Conjecture55Lean4Web.cyc_le_of_injective S.subtype S.subtype_injective

/-- The preceding result stated with the exact upstream FC definitions. -/
theorem fc_threshold_le_of_psl2_subgroup_index_pow_two
    {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (S : Subgroup G) (e : PSL2 p ≃* S)
    (k : ℕ) (hindex : S.index = 2 ^ k) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  simpa only [numPrimeFactors, Nat.card_eq_fintype_card] using
    threshold_le_of_psl2_subgroup_index_pow_two hp S e k hindex

/-- In particular, the bound holds when the PSL₂ subgroup has index one or two. -/
theorem fc_threshold_le_of_psl2_subgroup_index_one_or_two
    {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (S : Subgroup G) (e : PSL2 p ≃* S)
    (hindex : S.index = 1 ∨ S.index = 2) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  rcases hindex with h1 | h2
  · exact fc_threshold_le_of_psl2_subgroup_index_pow_two hp S e 0 (by simpa using h1)
  · exact fc_threshold_le_of_psl2_subgroup_index_pow_two hp S e 1 (by simpa using h2)


#print axioms primeFactors_eq_of_index_pow_two
#print axioms two_dvd_card_psl2
#print axioms threshold_le_of_psl2_subgroup_index_pow_two
#print axioms fc_threshold_le_of_psl2_subgroup_index_pow_two
#print axioms fc_threshold_le_of_psl2_subgroup_index_one_or_two
end Conjecture55Lean4Web.PSL2Extensions
