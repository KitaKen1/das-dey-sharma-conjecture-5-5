import Conjecture55Foundation

/-! The arithmetic gain from a proper odd normalizer index greater than three. -/

open scoped BigOperators
namespace Conjecture55OddSquarefree

theorem divisors_card_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne_zero]
  have he : (∏ p ∈ n.primeFactors, (n.factorization p + 1)) =
      ∏ _p ∈ n.primeFactors, 2 := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hn
      (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1]
  rw [he, Finset.prod_const]

theorem exists_prime_ge_five {n : ℕ} (hn : Squarefree n) (ho : Odd n) (h5 : 5 ≤ n) :
    ∃ p ∈ n.primeFactors, 5 ≤ p := by
  by_contra h
  push Not at h
  have hs : n.primeFactors ⊆ {3} := by
    intro p hp
    have hprime := (Nat.mem_primeFactors.mp hp).1
    have hd := (Nat.mem_primeFactors.mp hp).2.1
    have h2 : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ hd)
    have h4 : p ≠ 4 := by intro he; subst p; norm_num at hprime
    have := h p hp
    have := hprime.two_le
    simp only [Finset.mem_singleton]
    omega
  have hd : n ∣ 3 := by
    rw [← Nat.prod_primeFactors_of_squarefree hn]
    have hprod := Finset.prod_dvd_prod_of_subset n.primeFactors {3} (fun p : ℕ => p) hs
    simpa using hprod
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

/-- A nontrivial odd squarefree index other than three contributes a factor
at least 5/2 relative to its number of divisors. -/
theorem five_mul_divisors_le_two_mul {n : ℕ}
    (hn : Squarefree n) (ho : Odd n) (h5 : 5 ≤ n) :
    5 * n.divisors.card ≤ 2 * n := by
  obtain ⟨p, hp, hp5⟩ := exists_prime_ge_five hn ho h5
  have hcard := Finset.card_erase_add_one hp
  have hsmall : 2 ^ (n.primeFactors.erase p).card ≤
      ∏ q ∈ n.primeFactors.erase p, q := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by omega)
    intro q hq
    exact (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hq)).1.two_le
  have hprod : n = p * ∏ q ∈ n.primeFactors.erase p, q := by
    calc
      n = ∏ q ∈ n.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hn).symm
      _ = _ := (Finset.mul_prod_erase _ (fun q : ℕ => q) hp).symm
  have hb := Nat.mul_le_mul_right (∏ q ∈ n.primeFactors.erase p, q) hp5
  rw [divisors_card_of_squarefree hn, ← hcard, pow_succ]
  nlinarith

theorem normalizer_gain {m c n : ℕ}
    (hm : Squarefree m) (ho : Odd n) (h5 : 5 ≤ n) (hfactor : m = c * n) :
    5 * m.divisors.card ≤ 2 * (n * c.divisors.card) := by
  have hn : Squarefree n := Squarefree.squarefree_of_dvd
    (by rw [hfactor]; exact dvd_mul_left _ _) hm
  have hc : c.Coprime n := by
    exact Nat.coprime_of_squarefree_mul (hfactor ▸ hm)
  rw [hfactor, hc.card_divisors_mul]
  have h := five_mul_divisors_le_two_mul hn ho h5
  nlinarith

#print axioms divisors_card_of_squarefree
#print axioms five_mul_divisors_le_two_mul
#print axioms normalizer_gain
end Conjecture55OddSquarefree
