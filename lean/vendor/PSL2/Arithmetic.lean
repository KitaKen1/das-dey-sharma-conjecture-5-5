import Mathlib

namespace Conjecture55Arithmetic

/-- If a positive integer is a multiple of six and exceeds six, the product
of one factor of two for each distinct prime factor is at most a third of it. -/
theorem three_mul_two_pow_card_primeFactors_le (n : ℕ) (hn : 6 < n) (h6 : 6 ∣ n) :
    3 * 2 ^ n.primeFactors.card ≤ n := by
  have hn0 : n ≠ 0 := by omega
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num) h6, hn0⟩
  have h3 : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_trans (by norm_num) h6, hn0⟩
  by_cases hs : n.primeFactors ⊆ {2, 3}
  · have heq : n.primeFactors = {2, 3} := by
      apply Finset.Subset.antisymm hs
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    rw [heq]
    norm_num
    obtain ⟨k, rfl⟩ := h6
    omega
  · obtain ⟨q, hq, hq23⟩ := Finset.not_subset.mp hs
    have hqs : q ≠ 2 ∧ q ≠ 3 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hq23
    have hq2 := hqs.1
    have hq3 := hqs.2
    have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
    have hq5 : 5 ≤ q := by
      have hqge := hqprime.two_le
      have hq4 : q ≠ 4 := by intro h; subst q; norm_num at hqprime
      omega
    have h32 : 3 ∈ n.primeFactors.erase 2 := by simp [h3]
    have hq32 : q ∈ (n.primeFactors.erase 2).erase 3 := by simp [hq, hq2, hq3]
    let s := ((n.primeFactors.erase 2).erase 3).erase q
    have hcard : n.primeFactors.card = s.card + 3 := by
      have hA := Finset.card_erase_add_one h2
      have hB := Finset.card_erase_add_one h32
      have hC := Finset.card_erase_add_one hq32
      dsimp [s]
      omega
    have hprod : (∏ x ∈ n.primeFactors, x) = 6 * q * ∏ x ∈ s, x := by
      rw [← Finset.mul_prod_erase _ _ h2, ← Finset.mul_prod_erase _ _ h32,
        ← Finset.mul_prod_erase _ _ hq32]
      dsimp [s]
      ring
    have hsmall : 2 ^ s.card ≤ ∏ x ∈ s, x := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun _ _ => by omega)
      intro x hx
      have hxn : x ∈ n.primeFactors :=
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      exact (Nat.mem_primeFactors.mp hxn).1.two_le
    calc
      3 * 2 ^ n.primeFactors.card = 24 * 2 ^ s.card := by rw [hcard, pow_add]; ring
      _ ≤ 24 * ∏ x ∈ s, x := Nat.mul_le_mul_left 24 hsmall
      _ ≤ 6 * q * ∏ x ∈ s, x := Nat.mul_le_mul_right _ (by omega)
      _ = ∏ x ∈ n.primeFactors, x := hprod.symm
      _ ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)

/-- Prime squares above three are congruent to one modulo twenty-four. -/
theorem prime_sq_mod_twentyfour (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ^ 2 % 24 = 1 := by
  have hp2 : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).mpr (by omega)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have heq : p = 3 := (hp.dvd_iff_eq (by omega)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  rw [Nat.pow_mod]
  have hlt : p % 24 < 24 := Nat.mod_lt _ (by omega)
  interval_cases h : p % 24 <;> omega

/-- The arithmetic PSL₂ threshold, using its numerical order formula only.
The theorem makes no group-theoretic subgroup-count assumptions. -/
theorem psl2_primeFactor_threshold (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    2 ^ ((p * (p ^ 2 - 1) / 2).primeFactors.card + 2) < p ^ 2 + p + 2 := by
  have hmod := prime_sq_mod_twentyfour p hp (by omega)
  have h24 : 24 ∣ p ^ 2 - 1 := by omega
  obtain ⟨k, hk⟩ := h24
  let n := 6 * k
  have hNval : p ^ 2 - 1 = 4 * n := by dsimp [n]; omega
  have hpSq : 1 ≤ p ^ 2 := by nlinarith
  have hN6 : 6 ∣ n := ⟨k, rfl⟩
  have hNgt : 6 < n := by dsimp [n]; nlinarith [Nat.sub_add_cancel hpSq]
  have hN0 : n ≠ 0 := by omega
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num) hN6, hN0⟩
  have horder : p * (p ^ 2 - 1) / 2 = p * (2 * n) := by
    rw [hNval, show p * (4 * n) = 2 * (p * (2 * n)) by ring]
    omega
  have hpf2N : (2 * n).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_mul (by omega) hN0, Nat.prime_two.primeFactors]
    exact Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr h2)
  have hcard : (p * (p ^ 2 - 1) / 2).primeFactors.card ≤ n.primeFactors.card + 1 := by
    rw [horder, Nat.primeFactors_mul hp.ne_zero (by omega), hp.primeFactors, hpf2N]
    simpa using Finset.card_insert_le p n.primeFactors
  have hpow : 2 ^ ((p * (p ^ 2 - 1) / 2).primeFactors.card + 2) ≤
      8 * 2 ^ n.primeFactors.card := by
    calc
      _ ≤ 2 ^ (n.primeFactors.card + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 8 * 2 ^ n.primeFactors.card := by rw [pow_add]; ring
  have hbound := three_mul_two_pow_card_primeFactors_le n hNgt hN6
  nlinarith [Nat.sub_add_cancel hpSq]

/-- The exceptional smallest prime attains the numerical threshold exactly. -/
theorem psl2_five_primeFactor_threshold :
    2 ^ ((5 * (5 ^ 2 - 1) / 2).primeFactors.card + 2) = 5 ^ 2 + 5 + 2 := by
  have h60 : (60 : ℕ).primeFactors = {2, 3, 5} := by
    rw [show (60 : ℕ) = 2 * (2 * (3 * 5)) by norm_num]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num)]
    norm_num [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors,
      (by norm_num : Nat.Prime 5).primeFactors]
    decide
  change 2 ^ ((60 : ℕ).primeFactors.card + 2) = 32
  rw [h60]
  norm_num

/-- All primes at least five satisfy the threshold, including the equality
at five and the strict bound above it. -/
theorem psl2_primeFactor_threshold_le (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    2 ^ ((p * (p ^ 2 - 1) / 2).primeFactors.card + 2) ≤ p ^ 2 + p + 2 := by
  by_cases h5 : p = 5
  · subst p
    exact psl2_five_primeFactor_threshold.le
  · have h6 : p ≠ 6 := by intro h; subst p; norm_num at hp
    exact (psl2_primeFactor_threshold p hp (by omega)).le

/-- Division form of the distinct-prime estimate. -/
theorem two_pow_card_primeFactors_le_div_three (n : ℕ) (hn : 6 < n) (h6 : 6 ∣ n) :
    2 ^ n.primeFactors.card ≤ n / 3 := by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  simpa [Nat.mul_comm] using three_mul_two_pow_card_primeFactors_le n hn h6

/-- Adding a positive power of a new prime increases the number of distinct
prime factors by exactly one. -/
theorem card_primeFactors_prime_pow_mul_of_not_dvd
    (p k n : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hn : 0 < n) (hpn : ¬p ∣ n) :
    (p ^ k * n).primeFactors.card = n.primeFactors.card + 1 := by
  have hnotmem : p ∉ n.primeFactors := by
    intro h
    exact hpn (Nat.mem_primeFactors.mp h).2.1
  rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (by omega),
    Nat.primeFactors_prime_pow (by omega) hp]
  simp [hnotmem]

/-- A positive power of an already present prime does not change the number
of distinct prime factors. -/
theorem card_primeFactors_prime_pow_mul_of_dvd
    (p k n : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hn : 0 < n) (hpn : p ∣ n) :
    (p ^ k * n).primeFactors.card = n.primeFactors.card := by
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
  rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (by omega),
    Nat.primeFactors_prime_pow (by omega) hp]
  simp [hmem]

#print axioms card_primeFactors_prime_pow_mul_of_not_dvd
#print axioms card_primeFactors_prime_pow_mul_of_dvd
#print axioms psl2_five_primeFactor_threshold
#print axioms psl2_primeFactor_threshold_le
#print axioms two_pow_card_primeFactors_le_div_three
#print axioms psl2_primeFactor_threshold
#print axioms three_mul_two_pow_card_primeFactors_le
#print axioms prime_sq_mod_twentyfour
end Conjecture55Arithmetic
