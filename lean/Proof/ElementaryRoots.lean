/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

import ComparisonRoots

/-!
# Root counts when no element order is divisible by four

Ordinary root lower bounds suffice for the bound by eight times the number
of divisors of the odd part; no enhanced root bound is assumed.
-/

namespace RootWeights
noncomputable section

theorem card_roots_mono_of_dvd {G : Type*} [Group G] [Finite G]
    {d e : ℕ} (hde : d ∣ e) :
    Nat.card {x : G // x ^ d = 1} ≤ Nat.card {x : G // x ^ e = 1} := by
  let f : {x : G // x ^ d = 1} → {x : G // x ^ e = 1} := fun x =>
    ⟨x, orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_iff_pow_eq_one.mpr x.2).trans hde)⟩
  apply Nat.card_le_card_of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : {x : G // x ^ e = 1} => z.val) h

theorem square_eq_one_of_fourth_eq_one_of_no_four_order
    {G : Type*} [Group G] (hno4 : ∀ x : G, ¬ 4 ∣ orderOf x)
    (x : G) (hx : x ^ 4 = 1) : x ^ 2 = 1 := by
  have hd : orderOf x ∣ 2 ^ 2 := by
    simpa using orderOf_dvd_iff_pow_eq_one.mpr hx
  obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hk1 : k ≤ 1 := by
    by_contra h
    have hk2 : k = 2 := by omega
    apply hno4 x
    rw [heq, hk2]
    norm_num
  exact orderOf_dvd_iff_pow_eq_one.mp (heq ▸ pow_dvd_pow 2 hk1)

theorem card_roots_four_mul_eq_two_mul
    {G : Type*} [Group G] (hno4 : ∀ x : G, ¬ 4 ∣ orderOf x) (d : ℕ) :
    Nat.card {x : G // x ^ (4 * d) = 1} =
      Nat.card {x : G // x ^ (2 * d) = 1} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  constructor
  · intro hx
    have h4 : (x ^ d) ^ 4 = 1 := by simpa [pow_mul, mul_comm] using hx
    simpa [pow_mul, mul_comm] using
      square_eq_one_of_fourth_eq_one_of_no_four_order hno4 (x ^ d) h4
  · intro hx
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_iff_pow_eq_one.mpr hx).trans (by use 2; ring))

theorem card_roots_two_pow_mul_eq_two_mul
    {G : Type*} [Group G] (hno4 : ∀ x : G, ¬ 4 ∣ orderOf x) (k d : ℕ) :
    Nat.card {x : G // x ^ (2 ^ (k + 1) * d) = 1} =
      Nat.card {x : G // x ^ (2 * d) = 1} := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : 2 ^ (k + 1 + 1) * d = 4 * (2 ^ k * d) := by ring
    rw [he, card_roots_four_mul_eq_two_mul hno4]
    have he' : 2 * (2 ^ k * d) = 2 ^ (k + 1) * d := by ring
    rw [he']
    exact ih

theorem cyclic_count_ge_eight_mul_divisors_of_root_bounds
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 3 ≤ a) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hno4 : ∀ x : G, ¬ 4 ∣ orderOf x) :
    8 * m.divisors.card ≤ Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hmpos := hm.pos
  let : NeZero m := ⟨hmpos.ne'⟩
  let : NeZero (2 ^ a * m) := ⟨by positivity⟩
  let K := Multiplicative (ZMod m)
  let C := Multiplicative (ZMod 2)
  let B := ((K × C) × C) × C
  have hK : Nat.card K = m := by simp [K]
  have hC : Nat.card C = 2 := by simp [C]
  have hBcard : Nat.card B = 8 * m := by
    simp only [B, Nat.card_prod, hK, hC]
    ring
  have hBdvd : Nat.card B ∣ 2 ^ a * m := by
    rw [hBcard]
    refine Nat.mul_dvd_mul_right ⟨2 ^ (a - 3), ?_⟩ m
    have he : 3 + (a - 3) = a := by omega
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, he]
  have hsmall : ∀ d, d ∣ m → 8 * d ≤ Nat.card {x : G // x ^ (2 * d) = 1} := by
    intro d hd
    have h := hbase (2 ^ a * d) (by rw [hcard]; exact Nat.mul_dvd_mul_left _ hd)
    have he : a - 1 + 1 = a := by omega
    rw [← he, card_roots_two_pow_mul_eq_two_mul hno4] at h
    have hp : 8 ≤ 2 ^ (a - 1 + 1) := by
      rw [he]
      simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) ha
    exact (Nat.mul_le_mul_right d hp).trans h
  have hle := cyclic_count_le_of_root_counts
    (G := G) (H := B) (n := 2 ^ a * m)
    (fun x => hcard ▸ orderOf_dvd_natCard x)
    (fun x => (orderOf_dvd_natCard x).trans hBdvd) (by
      intro e he
      have hepos : 0 < e :=
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 (by positivity)
      change Nat.card {x : ((K × C) × C) × C // x ^ e = 1} ≤ _
      rw [card_roots_prod, card_roots_prod, card_roots_prod,
        card_roots_cyclic, card_roots_cyclic, hK, hC]
      by_cases h2e : 2 ∣ e
      · rw [Nat.gcd_eq_left h2e]
        have hdOdd : Odd (Nat.gcd m e) := hm.of_dvd_nat (Nat.gcd_dvd_left m e)
        have hd2e : 2 * Nat.gcd m e ∣ e :=
          hdOdd.coprime_two_left.mul_dvd_of_dvd_of_dvd h2e (Nat.gcd_dvd_right m e)
        have hl := (hsmall _ (Nat.gcd_dvd_left m e)).trans
          (card_roots_mono_of_dvd (G := G) hd2e)
        simpa [mul_assoc, mul_comm, mul_left_comm] using hl
      · rw [(Nat.prime_two.coprime_iff_not_dvd.mpr h2e).gcd_eq_one]
        simp only [mul_one]
        exact (Nat.gcd_le_right m hepos).trans
          (hbase e (hcard.symm ▸ (Nat.mem_divisors.mp he).1)))
  have hcB : Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups B) = 8 * m.divisors.card := by
    change Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups (((K × C) × C) × C)) = _
    rw [cyclic_count_prod_card_two hC, cyclic_count_prod_card_two hC,
      cyclic_count_prod_card_two hC, Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_divisors_card, hK]
    ring
  rwa [hcB] at hle

end
end RootWeights

#print axioms RootWeights.card_roots_mono_of_dvd
#print axioms RootWeights.square_eq_one_of_fourth_eq_one_of_no_four_order
#print axioms RootWeights.card_roots_four_mul_eq_two_mul
#print axioms RootWeights.card_roots_two_pow_mul_eq_two_mul
#print axioms RootWeights.cyclic_count_ge_eight_mul_divisors_of_root_bounds
