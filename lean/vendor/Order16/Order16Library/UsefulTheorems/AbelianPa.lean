/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.NormNum.Prime

/-!
# Abelian groups of order `p^a` and partitions of `a`

The structure theorem for finite abelian groups says that every finite abelian group is a product
of cyclic groups of prime-power order.  For a fixed prime `p`, this specialises to: every abelian
group of order `p^a` is isomorphic to a product `∏ ℤ/p^λᵢ` where the exponents `λᵢ` form a
**partition of `a`**.

This file packages the *exhaustiveness* half of that correspondence as a reusable engine:

* `partitionGroup p lam` — the abelian group `∏ ℤ/p^λᵢ` attached to a partition
  `lam : Nat.Partition a` (indexed over the parts of `lam`);
* `card_partitionGroup` — it has order `p^a`;
* `abelian_pa_classification` — **every** abelian group of order `p^a` is isomorphic to
  `partitionGroup p lam` for *some* partition `lam` of `a`.

This reduces the abelian part of any `p^a` classification to enumerating the partitions of `a`
(e.g. orders `8, 16, 27, 32, 81, …`).  The *injective* half (different partitions give
non-isomorphic groups) is left for a separate development.
-/

namespace Smallgroups.UsefulTheorems

open scoped BigOperators

/-! ### Small reusable equivalences -/

/-- Reindex a dependent product of multiplicative structures along an equivalence of index types. -/
def mulEquivPiCongrLeft' {ι κ : Type*} (A : ι → Type*) [∀ i, Mul (A i)] (e : ι ≃ κ) :
    (∀ i, A i) ≃* (∀ j, A (e.symm j)) :=
  { Equiv.piCongrLeft' A e with map_mul' := fun _ _ => rfl }

/-- An equality of moduli gives an isomorphism of the corresponding multiplicative `ZMod` groups. -/
def multZmodCongr {m n : ℕ} (h : m = n) :
    Multiplicative (ZMod m) ≃* Multiplicative (ZMod n) := by
  cases h; exact MulEquiv.refl _

/-- `Finset.univ.val.map (l.get)` is just `l` as a multiset. -/
theorem map_get_univ {α : Type*} (l : List α) :
    Multiset.map l.get Finset.univ.val = (l : Multiset α) := by
  rw [Finset.val_univ_fin, Multiset.map_coe, ← List.ofFn_eq_map, List.ofFn_get]

/-- The number of indices mapping to `v` is the multiplicity of `v` in the value-multiset. -/
private theorem card_fiber_eq_count {X : Type*} [Fintype X] (f : X → ℕ) (v : ℕ) :
    Fintype.card {i // f i = v} = Multiset.count v (Multiset.map f Finset.univ.val) := by
  classical
  rw [Multiset.count_map, Fintype.card_subtype, ← Finset.card_val, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro a _
  exact eq_comm

/-- **Value-preserving bijection from equal value-multisets.** If two finite-indexed families of
naturals have the same multiset of values, there is a bijection of the index sets matching the
values. -/
theorem exists_equiv_of_map_univ_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ι → ℕ) (l : κ → ℕ)
    (h : Multiset.map k Finset.univ.val = Multiset.map l Finset.univ.val) :
    ∃ σ : ι ≃ κ, ∀ i, l (σ i) = k i := by
  classical
  have hfib : ∀ v, Fintype.card {i // k i = v} = Fintype.card {j // l j = v} := by
    intro v; rw [card_fiber_eq_count k v, card_fiber_eq_count l v, h]
  exact ⟨Equiv.ofFiberEquiv (fun v => Fintype.equivOfCardEq (hfib v)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

/-! ### The group attached to a partition -/

/-- The abelian group `∏ ℤ/p^λᵢ` attached to a partition `lam` of `a`, indexed over its parts. -/
abbrev partitionGroup (p : ℕ) {a : ℕ} (lam : Nat.Partition a) : Type :=
  ∀ i : Fin lam.parts.toList.length, Multiplicative (ZMod (p ^ lam.parts.toList.get i))

/-- `partitionGroup p lam` has order `p^a`. -/
theorem card_partitionGroup (p : ℕ) [Fact p.Prime] {a : ℕ} (lam : Nat.Partition a) :
    Nat.card (partitionGroup p lam) = p ^ a := by
  classical
  set L := lam.parts.toList with hL
  have hp0 : p ≠ 0 := (Fact.out (p := p.Prime)).pos.ne'
  haveI : ∀ j : Fin L.length, NeZero (p ^ L.get j) := fun j => ⟨pow_ne_zero _ hp0⟩
  rw [partitionGroup, Nat.card_pi]
  have hcard : ∀ j : Fin L.length,
      Nat.card (Multiplicative (ZMod (p ^ L.get j))) = p ^ L.get j := by
    intro j; rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [Finset.prod_congr rfl (fun j _ => hcard j), Finset.prod_pow_eq_pow_sum]
  congr 1
  have h1 : (∑ j : Fin L.length, L.get j) = L.sum := by
    rw [← List.sum_ofFn, List.ofFn_get]
  rw [h1, hL, Multiset.sum_toList, lam.parts_sum]

/-! ### Exhaustiveness: every abelian group of order `p^a` is some `partitionGroup` -/

/-- **Every abelian group of order `p^a` is isomorphic to `partitionGroup p lam` for some partition
`lam` of `a`.** This is the structure theorem for finite abelian groups, organised by the partition
of `a` recording the exponents of the cyclic factors. -/
theorem abelian_pa_classification (p a : ℕ) [Fact p.Prime] (G : Type*) [CommGroup G]
    (hcard : Nat.card G = p ^ a) :
    ∃ lam : Nat.Partition a, Nonempty (G ≃* partitionGroup p lam) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero a hp.pos.ne')
  obtain ⟨ι, fι, n, hn1, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  haveI : Fintype ι := fι
  haveI : ∀ i, NeZero (n i) := fun i => ⟨by have := hn1 i; omega⟩
  -- the factors multiply to `p ^ a`
  have hprod : ∏ i, n i = p ^ a := by
    have h1 : Nat.card G = ∏ i, n i := by
      rw [Nat.card_congr e.toEquiv, Nat.card_pi]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rw [hcard] at h1; exact h1.symm
  -- each factor is a power of `p` with exponent ≥ 1
  have hdvd : ∀ i, n i ∣ p ^ a := fun i => hprod ▸ Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  have hn_pow : ∀ i, ∃ m, 1 ≤ m ∧ n i = p ^ m := by
    intro i
    obtain ⟨m, _, hnm⟩ := (Nat.dvd_prime_pow hp).mp (hdvd i)
    refine ⟨m, ?_, hnm⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, pow_zero] at hnm; have := hn1 i; omega
    · exact h0
  choose K hK1 hKpow using hn_pow
  -- the exponents sum to `a`
  have hsumk : ∑ i, K i = a := by
    have hpe : p ^ (∑ i, K i) = p ^ a := by
      rw [← Finset.prod_pow_eq_pow_sum, ← hprod]
      exact Finset.prod_congr rfl (fun i _ => (hKpow i).symm)
    exact Nat.pow_right_injective hp.two_le hpe
  -- the partition recording the exponents
  set lam : Nat.Partition a :=
    { parts := Multiset.map K Finset.univ.val
      parts_pos := by
        intro i hi
        rw [Multiset.mem_map] at hi
        obtain ⟨j, _, rfl⟩ := hi
        exact hK1 j
      parts_sum := by
        show (Multiset.map K Finset.univ.val).sum = a
        rw [← hsumk]; rfl } with hlam
  refine ⟨lam, ?_⟩
  set L := lam.parts.toList with hLdef
  -- the structure-theorem index set and the partition's parts have the same value-multiset
  have hmapeq : Multiset.map K Finset.univ.val = Multiset.map L.get Finset.univ.val := by
    rw [map_get_univ L, hLdef, Multiset.coe_toList]
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_univ_eq K L.get hmapeq
  -- exponents match after reindexing
  have hexp : ∀ j, n (σ.symm j) = p ^ L.get j := by
    intro j
    rw [hKpow (σ.symm j)]
    congr 1
    rw [← hσ (σ.symm j), Equiv.apply_symm_apply]
  exact ⟨e.trans ((mulEquivPiCongrLeft' (fun i => Multiplicative (ZMod (n i))) σ).trans
    (MulEquiv.piCongrRight (fun j => multZmodCongr (hexp j))))⟩

end Smallgroups.UsefulTheorems
