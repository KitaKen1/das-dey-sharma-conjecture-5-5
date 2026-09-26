/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

import Conjecture55Foundation

/-!
# Cyclic subgroup counts as weighted root counts

The weights come from fibers in the unit group modulo a common exponent.
They are nonnegative, and root-count comparisons imply cyclic-count comparisons.
-/

open scoped BigOperators

namespace RootWeights
noncomputable section

def rootDivisor (n : ℕ) (u : (ZMod n)ˣ) : ℕ :=
  Nat.gcd n (((u : ZMod n) - 1).val)

theorem rootDivisor_dvd (n : ℕ) (u : (ZMod n)ˣ) : rootDivisor n u ∣ n :=
  Nat.gcd_dvd_left _ _

theorem dvd_rootDivisor_iff_unitsMap_eq_one {n r : ℕ} [NeZero n]
    (hr : r ∣ n) (u : (ZMod n)ˣ) :
    r ∣ rootDivisor n u ↔ ZMod.unitsMap hr u = 1 := by
  have hcast : ((((u : ZMod n) - 1).val : ℕ) : ZMod r) =
      (ZMod.castHom hr (ZMod r)) (u : ZMod n) - 1 := by
    have h := congrArg (ZMod.castHom hr (ZMod r))
      (ZMod.natCast_zmod_val ((u : ZMod n) - 1))
    simpa only [map_natCast, map_sub, map_one] using h
  rw [rootDivisor, Nat.dvd_gcd_iff, and_iff_right hr,
    ← ZMod.natCast_eq_zero_iff, hcast, sub_eq_zero]
  change ((ZMod.unitsMap hr u : ZMod r) = (1 : (ZMod r)ˣ)) ↔ _
  exact Units.ext_iff.symm

theorem card_kernel_unitsMap_mul_totient {n r : ℕ} [NeZero n]
    (hr : r ∣ n) :
    Nat.card (ZMod.unitsMap hr).ker * r.totient = n.totient := by
  have : NeZero r := ⟨fun hz => (NeZero.ne n) (Nat.eq_zero_of_zero_dvd (hz ▸ hr))⟩
  have hs := ZMod.unitsMap_surjective hr
  have hc := (ZMod.unitsMap hr).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs, Subgroup.card_top] at hc
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using hc

def rootKernelEquiv {n r : ℕ} [NeZero n] (hr : r ∣ n) :
    {u : (ZMod n)ˣ // r ∣ rootDivisor n u} ≃ (ZMod.unitsMap hr).ker :=
  Equiv.subtypeEquivRight (fun u => dvd_rootDivisor_iff_unitsMap_eq_one hr u)

theorem reciprocal_totient_eq_unit_average {n r : ℕ} [NeZero n]
    (hr : r ∣ n) :
    (1 : ℚ) / r.totient =
      (∑ u : (ZMod n)ˣ, if r ∣ rootDivisor n u then (1 : ℚ) else 0) / n.totient := by
  classical
  have hs : (∑ u : (ZMod n)ˣ, if r ∣ rootDivisor n u then (1 : ℚ) else 0) =
      (Nat.card (ZMod.unitsMap hr).ker : ℚ) := by
    rw [← Nat.card_congr (rootKernelEquiv hr)]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hs]
  have hc : (Nat.card (ZMod.unitsMap hr).ker : ℚ) * r.totient = n.totient := by
    exact_mod_cast card_kernel_unitsMap_mul_totient hr
  have hn : (n.totient : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  have hr0 : (r.totient : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hr (NeZero.pos n))).ne'
  field_simp
  simpa [mul_comm] using hc.symm

theorem cyclic_count_eq_unit_average
    {G : Type*} [Group G] [Fintype G] {n : ℕ} [NeZero n]
    (hG : ∀ x : G, orderOf x ∣ n) :
    (Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) : ℚ) =
      (∑ u : (ZMod n)ˣ, (Nat.card {x : G // x ^ (rootDivisor n u) = 1} : ℚ)) /
        n.totient := by
  classical
  rw [Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_sum]
  simp_rw [reciprocal_totient_eq_unit_average (hG _)]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [orderOf_dvd_iff_pow_eq_one]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem cyclic_count_le_of_root_counts
    {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    {n : ℕ} [NeZero n]
    (hG : ∀ x : G, orderOf x ∣ n) (hH : ∀ x : H, orderOf x ∣ n)
    (hroot : ∀ d ∈ n.divisors,
      Nat.card {x : H // x ^ d = 1} ≤ Nat.card {x : G // x ^ d = 1}) :
    Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups H) ≤ Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hq : (Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups H) : ℚ) ≤
      (Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) : ℚ) := by
    rw [cyclic_count_eq_unit_average hG, cyclic_count_eq_unit_average hH]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro u _
    exact Nat.cast_le.mpr (hroot _
      (Nat.mem_divisors.mpr ⟨rootDivisor_dvd n u, NeZero.ne n⟩))
  exact_mod_cast hq

def rootWeight (n d : ℕ) : ℚ :=
  (Nat.card {u : (ZMod n)ˣ // rootDivisor n u = d} : ℚ) / n.totient

theorem rootWeight_nonneg (n d : ℕ) : 0 ≤ rootWeight n d :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem cyclic_count_eq_weighted_roots
    {G : Type*} [Group G] [Fintype G] {n : ℕ} [NeZero n]
    (hG : ∀ x : G, orderOf x ∣ n) :
    (Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) : ℚ) =
      ∑ d ∈ n.divisors, rootWeight n d * Nat.card {x : G // x ^ d = 1} := by
  classical
  rw [cyclic_count_eq_unit_average hG]
  have hm (u : (ZMod n)ˣ) (_ : u ∈ Finset.univ) : rootDivisor n u ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨rootDivisor_dvd n u, NeZero.ne n⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have heq : (∑ u : (ZMod n)ˣ with rootDivisor n u = d,
      (Nat.card {x : G // x ^ rootDivisor n u = 1} : ℚ)) =
      ∑ _u : (ZMod n)ˣ with rootDivisor n _u = d,
        (Nat.card {x : G // x ^ d = 1} : ℚ) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [(Finset.mem_filter.mp hu).2]
  rw [heq]
  simp only [rootWeight, Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  ring

end
end RootWeights

#print axioms RootWeights.dvd_rootDivisor_iff_unitsMap_eq_one
#print axioms RootWeights.card_kernel_unitsMap_mul_totient
#print axioms RootWeights.reciprocal_totient_eq_unit_average
#print axioms RootWeights.cyclic_count_eq_unit_average
#print axioms RootWeights.cyclic_count_le_of_root_counts
#print axioms RootWeights.rootWeight_nonneg
#print axioms RootWeights.cyclic_count_eq_weighted_roots
