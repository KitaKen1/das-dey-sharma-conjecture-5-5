/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

import RootWeights

/-!
# Numerical cyclic-count bounds from root estimates

Ordinary and enhanced root lower bounds remain explicit hypotheses.
The comparison requires no order-divisibility bijection.
-/

open scoped BigOperators

namespace RootWeights
noncomputable section

-- The following three elementary count lemmas reuse the checked TwoFactor proof.
theorem totient_lcm_two (n : ℕ) : (Nat.lcm n 2).totient = n.totient := by
  by_cases h : 2 ∣ n
  · rw [Nat.lcm_eq_left h]
  · have hc : n.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h).symm
    rw [hc.lcm_eq_mul, Nat.mul_comm, Nat.totient_two_mul_of_odd]
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using h)

theorem totient_orderOf_prod_card_two
    {G H : Type*} [Group G] [Group H] (hH : Nat.card H = 2) (g : G) (h : H) :
    (orderOf (g,h)).totient = (orderOf g).totient := by
  have hd : orderOf h ∣ 2 := hH ▸ orderOf_dvd_natCard h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
  · simp [Prod.orderOf, hh]
  · simp [Prod.orderOf, hh, totient_lcm_two]

theorem cyclic_count_prod_card_two
    {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (hH : Nat.card H = 2) :
    Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups (G × H)) =
      2 * Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have heq : (Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups (G × H)) : ℚ) =
      2 * (Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) : ℚ) := by
    rw [Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_sum, Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_sum, Fintype.sum_prod_type]
    simp_rw [totient_orderOf_prod_card_two hH]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card, hH]
    simp only [Nat.cast_ofNat, ← Finset.mul_sum]
  exact_mod_cast heq

theorem card_roots_cyclic {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] (d : ℕ) :
    Nat.card {x : G // x ^ d = 1} = (Nat.card G).gcd d := by
  exact IsCyclic.card_powMonoidHom_ker G d

def rootsProdEquiv {G H : Type*} [Group G] [Group H] (d : ℕ) :
    {x : G × H // x ^ d = 1} ≃ {x : G // x ^ d = 1} × {x : H // x ^ d = 1} where
  toFun x := (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), Prod.ext x.1.2 x.2.2⟩
  left_inv _x := rfl
  right_inv _x := rfl

theorem card_roots_prod {G H : Type*} [Group G] [Group H] (d : ℕ) :
    Nat.card {x : G × H // x ^ d = 1} =
      Nat.card {x : G // x ^ d = 1} * Nat.card {x : H // x ^ d = 1} := by
  rw [Nat.card_congr (rootsProdEquiv d), Nat.card_prod]

theorem twice_gcd_le_of_not_dvd {N d : ℕ} (hd : 0 < d) (hnd : ¬ d ∣ N) :
    2 * Nat.gcd N d ≤ d := by
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_right N d
  have hg : 0 < Nat.gcd N d := Nat.gcd_pos_of_pos_right N hd
  have hk0 : k ≠ 0 := by intro h; simp [h] at hk; omega
  have hk1 : k ≠ 1 := by
    intro h
    apply hnd
    have he : d = Nat.gcd N d := by simpa [h] using hk
    rw [he]
    exact Nat.gcd_dvd_left N d
  have hk2 : 2 ≤ k := by omega
  nlinarith

theorem gcd_product_le_of_root_bounds
    {G : Type*} [Group G] [Finite G] {N d : ℕ} (hN : 0 < N)
    (hd : d ∣ 2 * N)
    (hbase : ∀ e, e ∣ 2 * N → e ≤ Nat.card {x : G // x ^ e = 1})
    (hdouble : ∀ e, e ∣ N → 2 ∣ e → 2 * e ≤ Nat.card {x : G // x ^ e = 1}) :
    Nat.gcd N d * Nat.gcd 2 d ≤ Nat.card {x : G // x ^ d = 1} := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by positivity)
  by_cases h2d : 2 ∣ d
  · rw [Nat.gcd_eq_left h2d]
    by_cases hdN : d ∣ N
    · rw [Nat.gcd_eq_right hdN, mul_comm]
      exact hdouble d hdN h2d
    · have hle : Nat.gcd N d * 2 ≤ d := by
        simpa [mul_comm] using twice_gcd_le_of_not_dvd hdpos hdN
      exact hle.trans (hbase d hd)
  · rw [(Nat.prime_two.coprime_iff_not_dvd.mpr h2d).gcd_eq_one, mul_one]
    exact (Nat.gcd_le_right N hdpos).trans (hbase d hd)

theorem cyclic_count_ge_twice_divisors_of_root_bounds
    {G : Type*} [Group G] [Fintype G] {N : ℕ} (hN : 0 < N)
    (hcard : Nat.card G = 2 * N)
    (hbase : ∀ e, e ∣ 2 * N → e ≤ Nat.card {x : G // x ^ e = 1})
    (hdouble : ∀ e, e ∣ N → 2 ∣ e → 2 * e ≤ Nat.card {x : G // x ^ e = 1}) :
    2 * N.divisors.card ≤ Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero (2 * N) := ⟨by positivity⟩
  let K := Multiplicative (ZMod N)
  let H := Multiplicative (ZMod 2)
  have hK : Nat.card K = N := by simp [K]
  have hH : Nat.card H = 2 := by simp [H]
  have hKH : Nat.card (K × H) = 2 * N := by rw [Nat.card_prod, hK, hH]; omega
  have hle := cyclic_count_le_of_root_counts
    (G := G) (H := K × H) (n := 2 * N)
    (fun x => hcard ▸ orderOf_dvd_natCard x)
    (fun x => hKH ▸ orderOf_dvd_natCard x) (by
      intro d hd
      rw [card_roots_prod, card_roots_cyclic, card_roots_cyclic, hK, hH]
      exact gcd_product_le_of_root_bounds hN (Nat.mem_divisors.mp hd).1 hbase hdouble)
  rw [cyclic_count_prod_card_two hH, Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_divisors_card, hK] at hle
  exact hle

theorem even_divisor_double_bound
    {G : Type*} [Group G] [Finite G] {a m e : ℕ} (ha : 1 ≤ a) (hm : Odd m)
    (he : e ∣ 2 ^ (a - 1) * m) (h2e : 2 ∣ e)
    (hdouble : ∀ d, d ∣ m → ∀ j, 1 ≤ j → j < a →
      2 ^ (j + 1) * d ≤ Nat.card {x : G // x ^ (2 ^ j * d) = 1}) :
    2 * e ≤ Nat.card {x : G // x ^ e = 1} := by
  have hmpos := hm.pos
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he (by positivity)
  obtain ⟨j, d, hdOdd, heq⟩ := Nat.exists_eq_two_pow_mul_odd hepos.ne'
  have hj1 : 1 ≤ j := by
    by_contra hj
    have hj0 : j = 0 := by omega
    have h2d : 2 ∣ d := by simpa [heq, hj0] using h2e
    exact hdOdd.not_two_dvd_nat h2d
  have hpow : 2 ^ j ∣ 2 ^ (a - 1) * m := by
    apply dvd_trans _ he
    rw [heq]
    exact dvd_mul_right _ _
  have hjle : j ≤ a - 1 :=
    (Nat.pow_dvd_pow_iff_le_right Nat.prime_two.one_lt).mp
      ((hm.coprime_two_left.pow_left j).dvd_of_dvd_mul_right hpow)
  have hdm : d ∣ m := by
    apply (hdOdd.coprime_two_right.pow_right (a - 1)).dvd_of_dvd_mul_left
    apply dvd_trans _ he
    rw [heq]
    exact dvd_mul_left _ _
  have hb := hdouble d hdm j hj1 (by omega)
  simpa [heq, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hb

theorem cyclic_count_ge_two_mul_exponent_mul_divisors
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hdouble : ∀ d, d ∣ m → ∀ j, 1 ≤ j → j < a →
      2 ^ (j + 1) * d ≤ Nat.card {x : G // x ^ (2 ^ j * d) = 1}) :
    2 * a * m.divisors.card ≤ Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hmpos := hm.pos
  have hn : 0 < 2 ^ (a - 1) * m := by positivity
  have hcard' : Nat.card G = 2 * (2 ^ (a - 1) * m) := by
    have hpow : 2 ^ (a - 1) * 2 = 2 ^ a := by
      rw [← pow_succ, Nat.sub_add_cancel ha]
    rw [hcard, ← hpow]
    ring
  have hdcount : (2 ^ (a - 1) * m).divisors.card = a * m.divisors.card := by
    rw [(hm.coprime_two_left.pow_left (a - 1)).card_divisors_mul,
      Nat.divisors_prime_pow Nat.prime_two]
    simp [Nat.sub_add_cancel ha]
  have hb := cyclic_count_ge_twice_divisors_of_root_bounds hn hcard'
    (fun e he => hbase e (hcard'.symm ▸ he))
    (fun e he h2e => even_divisor_double_bound ha hm he h2e hdouble)
  simpa [hdcount, mul_assoc] using hb

end
end RootWeights

#print axioms RootWeights.card_roots_cyclic
#print axioms RootWeights.card_roots_prod
#print axioms RootWeights.twice_gcd_le_of_not_dvd
#print axioms RootWeights.gcd_product_le_of_root_bounds
#print axioms RootWeights.cyclic_count_ge_twice_divisors_of_root_bounds
#print axioms RootWeights.even_divisor_double_bound
#print axioms RootWeights.cyclic_count_ge_two_mul_exponent_mul_divisors
