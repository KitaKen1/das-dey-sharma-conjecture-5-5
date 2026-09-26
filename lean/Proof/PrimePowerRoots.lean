/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

import Mathlib

/-!
Elementary root-count lemmas for groups containing a noncyclic prime-power subgroup.
No root-count divisibility theorem or order-divisibility bijection is assumed.
-/

namespace AmiriNext

theorem pow_eq_one_of_prime_power_card_not_cyclic
    {K : Type*} [Group K] [Finite K] {p j : ℕ} (hp : p.Prime)
    (hcard : Nat.card K = p ^ (j + 1)) (hnc : ¬ IsCyclic K) (x : K) :
    x ^ (p ^ j) = 1 := by
  have hd : orderOf x ∣ p ^ (j + 1) := hcard ▸ orderOf_dvd_natCard x
  obtain ⟨k, hkj, hk⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hne : k ≠ j + 1 := by
    intro heq
    apply hnc
    exact isCyclic_of_orderOf_eq_card x (by simpa [heq, hcard] using hk)
  exact orderOf_dvd_iff_pow_eq_one.mp (hk ▸ pow_dvd_pow p (by omega))

theorem exists_noncyclic_prime_power_subgroup_in_roots
    {G : Type*} [Group G] [Finite G] {p r j : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hH : Nat.card H = p ^ r) (hnc : ¬ IsCyclic H)
    (hrj : r ≤ j + 1) (hdvd : p ^ (j + 1) ∣ Nat.card G) :
    ∃ K : Subgroup G, Nat.card K = p ^ (j + 1) ∧
      ∀ x : K, (x : G) ^ (p ^ j) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, hHK⟩ := Sylow.exists_subgroup_card_pow_prime_le p hdvd H hH hrj
  have hKnc : ¬ IsCyclic K := by
    intro hKcyc
    let : IsCyclic K := hKcyc
    exact hnc (isCyclic_of_injective (Subgroup.inclusion hHK)
      (Subgroup.inclusion_injective hHK))
  refine ⟨K, hK, fun x => ?_⟩
  exact congrArg Subtype.val (pow_eq_one_of_prime_power_card_not_cyclic hp hK hKnc x)

theorem prime_power_le_card_roots_of_noncyclic_subgroup
    {G : Type*} [Group G] [Finite G] {p r j d : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hH : Nat.card H = p ^ r) (hnc : ¬ IsCyclic H)
    (hrj : r ≤ j + 1) (hdvd : p ^ (j + 1) ∣ Nat.card G) :
    p ^ (j + 1) ≤ Nat.card {x : G // x ^ (p ^ j * d) = 1} := by
  obtain ⟨K, hK, hroot⟩ :=
    exists_noncyclic_prime_power_subgroup_in_roots hp H hH hnc hrj hdvd
  let f : K → {x : G // x ^ (p ^ j * d) = 1} := fun x =>
    ⟨x, by rw [pow_mul, hroot x, one_pow]⟩
  have hf : Function.Injective f := by
    intro x y heq
    apply Subtype.ext
    exact congrArg (fun z : {x : G // x ^ (p ^ j * d) = 1} => z.val) heq
  simpa [hK] using Nat.card_le_card_of_injective f hf

theorem no_subgroup_of_card_eq_exponent_contains_all_roots
    {G : Type*} [Group G] [Finite G] {p r j d : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hH : Nat.card H = p ^ r) (hnc : ¬ IsCyclic H)
    (hrj : r ≤ j + 1) (hdvd : p ^ (j + 1) ∣ Nat.card G) (hpd : ¬ p ∣ d)
    (N : Subgroup G) (hN : Nat.card N = p ^ j * d)
    (hroot : ∀ x : G, x ^ (p ^ j * d) = 1 → x ∈ N) : False := by
  obtain ⟨K, hK, hKroot⟩ :=
    exists_noncyclic_prime_power_subgroup_in_roots hp H hH hnc hrj hdvd
  have hKN : K ≤ N := by
    intro x hx
    apply hroot x
    rw [pow_mul, hKroot ⟨x, hx⟩, one_pow]
  have hd : p ^ (j + 1) ∣ p ^ j * d := by
    simpa [hK, hN] using Subgroup.card_dvd_of_le hKN
  apply hpd
  rw [pow_succ] at hd
  exact (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos j)).mp hd

end AmiriNext

#print axioms AmiriNext.pow_eq_one_of_prime_power_card_not_cyclic
#print axioms AmiriNext.exists_noncyclic_prime_power_subgroup_in_roots
#print axioms AmiriNext.prime_power_le_card_roots_of_noncyclic_subgroup
#print axioms AmiriNext.no_subgroup_of_card_eq_exponent_contains_all_roots
