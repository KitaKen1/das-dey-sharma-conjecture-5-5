/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.AbelianPa
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Distinct partitions give non-isomorphic abelian groups

This file completes the correspondence started in `AbelianPa.lean`: it proves the **injective**
half, that `partitionGroup p lam ≃* partitionGroup p mu` forces `lam = mu`. Together with the
exhaustiveness result `abelian_pa_classification`, this makes the partitions of `a` a genuine
complete and irredundant list of the abelian groups of order `p^a` — so there are exactly
`Nat.card (Nat.Partition a)` of them.

The separating invariant is the **`p^j`-torsion count** `torsionCard G (p^j) = #{x : x^(p^j) = 1}`.
For `partitionGroup p lam` this equals `p ^ (∑ᵢ min j λᵢ)`, and the sequence `j ↦ ∑ᵢ min j λᵢ`
determines the multiset of parts (it is the partial-sum form of the conjugate partition).
-/

namespace Smallgroups.UsefulTheorems

open scoped BigOperators

/-! ### The torsion-count invariant -/

/-- The `m`-torsion count of a monoid: the number of elements killed by the `m`-th power. -/
noncomputable def torsionCard (G : Type*) [Monoid G] (m : ℕ) : ℕ := Nat.card {x : G // x ^ m = 1}

/-- The torsion count is an isomorphism invariant. -/
theorem torsionCard_congr {G H : Type*} [Monoid G] [Monoid H] (m : ℕ) (e : G ≃* H) :
    torsionCard G m = torsionCard H m := by
  refine Nat.card_congr (e.toEquiv.subtypeEquiv (fun x => ?_))
  change x ^ m = 1 ↔ (e x) ^ m = 1
  rw [← map_pow]
  exact (map_eq_one_iff e e.injective).symm

/-- The torsion count of a finite product is the product of the torsion counts. -/
theorem torsionCard_pi {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, Monoid (G i)] (m : ℕ) :
    torsionCard (∀ i, G i) m = ∏ i, torsionCard (G i) m := by
  unfold torsionCard
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Equiv.subtypeEquivRight (fun x => ?_)).trans Equiv.subtypePiEquivPi)
  rw [funext_iff]
  refine forall_congr' (fun i => ?_)
  rw [Pi.pow_apply, Pi.one_apply]

/-- For a finite cyclic group, the torsion count is a gcd. -/
theorem torsionCard_eq_gcd_of_isCyclic (G : Type*) [CommGroup G] [Finite G] [IsCyclic G] (m : ℕ) :
    torsionCard G m = (Nat.card G).gcd m := by
  rw [← IsCyclic.card_powMonoidHom_ker G m]
  unfold torsionCard
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
  rw [MonoidHom.mem_ker, powMonoidHom_apply]

/-! ### The torsion count of `partitionGroup` -/

/-- `gcd (p^k) (p^j) = p ^ min k j`. -/
private theorem gcd_pow_pow (p k j : ℕ) : Nat.gcd (p ^ k) (p ^ j) = p ^ min k j := by
  rcases le_total k j with h | h
  · rw [Nat.gcd_eq_left (pow_dvd_pow p h), min_eq_left h]
  · rw [Nat.gcd_eq_right (pow_dvd_pow p h), min_eq_right h]

/-- The `p^j`-torsion of `partitionGroup p lam` has size `p ^ (∑ᵢ min j λᵢ)`. -/
theorem torsionCard_partitionGroup (p : ℕ) [Fact p.Prime] {a : ℕ} (lam : Nat.Partition a)
    (j : ℕ) :
    torsionCard (partitionGroup p lam) (p ^ j) = p ^ (lam.parts.map (min j)).sum := by
  classical
  have hp : p.Prime := Fact.out
  set L := lam.parts.toList with hL
  rw [torsionCard_pi]
  have hfac : ∀ i : Fin L.length,
      torsionCard (Multiplicative (ZMod (p ^ L.get i))) (p ^ j) = p ^ min j (L.get i) := by
    intro i
    haveI : NeZero (p ^ L.get i) := ⟨pow_ne_zero _ hp.pos.ne'⟩
    rw [torsionCard_eq_gcd_of_isCyclic, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card, gcd_pow_pow, Nat.min_comm]
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_pow_eq_pow_sum]
  congr 1
  -- `∑ i, min j (L.get i) = (lam.parts.map (min j)).sum`
  have hoffn : L.map (min j) = List.ofFn (fun i : Fin L.length => min j (L.get i)) := by
    conv_lhs => rw [← List.ofFn_get L]
    rw [List.map_ofFn]
    rfl
  calc (∑ i : Fin L.length, min j (L.get i))
      = (List.ofFn (fun i : Fin L.length => min j (L.get i))).sum := List.sum_ofFn.symm
    _ = (L.map (min j)).sum := by rw [hoffn]
    _ = (lam.parts.map (min j)).sum := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, hL, Multiset.coe_toList]

/-! ### Recovering a partition from its min-sums -/

/-- Indicator-sum form of `countP`. -/
private theorem sum_map_ite_eq_countP (s : Multiset ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (s.map (fun x => if q x then 1 else 0)).sum = s.countP q := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.countP_cons]
    exact Nat.add_comm _ _

/-- If two multisets of positive naturals have the same `min j`-sums for every `j`, they are
equal. (The `min j`-sums recover, via differences, the number of parts `≥ j`, hence every count.) -/
theorem multiset_eq_of_min_sum_eq {s t : Multiset ℕ} (hs : (0 : ℕ) ∉ s) (ht : (0 : ℕ) ∉ t)
    (h : ∀ j, (s.map (min j)).sum = (t.map (min j)).sum) : s = t := by
  classical
  -- the `min (j+1)`-sum exceeds the `min j`-sum by the number of parts `≥ j+1`
  have hrec : ∀ (u : Multiset ℕ) (j : ℕ),
      (u.map (min (j + 1))).sum = (u.map (min j)).sum + u.countP (fun x => j + 1 ≤ x) := by
    intro u j
    rw [← sum_map_ite_eq_countP, ← Multiset.sum_map_add]
    congr 1
    refine Multiset.map_congr rfl (fun x _ => ?_)
    split <;> omega
  -- hence the number of parts `≥ j+1` agrees for all `j`
  have hcount : ∀ j, s.countP (fun x => j + 1 ≤ x) = t.countP (fun x => j + 1 ≤ x) := by
    intro j
    have e1 := hrec s j
    have e2 := hrec t j
    have h1 := h (j + 1)
    have h2 := h j
    omega
  -- the parts `≥ v` split into the parts `= v` and the parts `≥ v+1`
  have hsplit : ∀ (u : Multiset ℕ) (v : ℕ),
      u.countP (fun x => v ≤ x) = u.count v + u.countP (fun x => v + 1 ≤ x) := by
    intro u v
    induction u using Multiset.induction with
    | empty => simp
    | cons a u ih =>
      rw [Multiset.countP_cons, Multiset.count_cons, Multiset.countP_cons, ih]
      split_ifs <;> omega
  -- conclude via count extensionality
  ext v
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [Multiset.count_eq_zero_of_notMem hs, Multiset.count_eq_zero_of_notMem ht]
  · have hs1 := hsplit s v
    have ht1 := hsplit t v
    have c1 := hcount (v - 1)
    have c2 := hcount v
    rw [Nat.sub_add_cancel hv] at c1
    omega

/-! ### Distinctness and the headline correspondence -/

/-- **Distinct partitions give non-isomorphic groups.** -/
theorem partitionGroup_distinct (p : ℕ) [Fact p.Prime] {a : ℕ} {lam mu : Nat.Partition a}
    (h : Nonempty (partitionGroup p lam ≃* partitionGroup p mu)) : lam = mu := by
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := h
  -- equal torsion counts for every `j`
  have hmin : ∀ j, (lam.parts.map (min j)).sum = (mu.parts.map (min j)).sum := by
    intro j
    have := torsionCard_congr (p ^ j) e
    rw [torsionCard_partitionGroup, torsionCard_partitionGroup] at this
    exact Nat.pow_right_injective hp.two_le this
  -- recover equality of the parts, hence of the partitions
  refine Nat.Partition.ext ?_
  exact multiset_eq_of_min_sum_eq (fun hm => absurd (lam.parts_pos hm) (lt_irrefl 0))
    (fun hm => absurd (mu.parts_pos hm) (lt_irrefl 0)) hmin

/-- **The 1-1 correspondence.** Two partition-groups are isomorphic iff the partitions are equal. -/
theorem partitionGroup_mulEquiv_iff (p : ℕ) [Fact p.Prime] {a : ℕ} {lam mu : Nat.Partition a} :
    Nonempty (partitionGroup p lam ≃* partitionGroup p mu) ↔ lam = mu := by
  refine ⟨partitionGroup_distinct p, ?_⟩
  rintro rfl
  exact ⟨MulEquiv.refl _⟩

/-- **The count of abelian groups of order `p^a`.** Any complete, pairwise non-isomorphic list of
abelian groups of order `p^a` has length `Nat.card (Nat.Partition a)`, the number of partitions of
`a`. (The analogue of `IsClassif.card_unique`, restricted to abelian groups.) -/
theorem abelian_classCount (p : ℕ) [Fact p.Prime] {a k : ℕ} (rep : Fin k → Type)
    [∀ i, CommGroup (rep i)]
    (hcard : ∀ i, Nat.card (rep i) = p ^ a)
    (hcomplete : ∀ (G : Type) [CommGroup G], Nat.card G = p ^ a → ∃ i, Nonempty (G ≃* rep i))
    (hdistinct : ∀ i j, Nonempty (rep i ≃* rep j) → i = j) :
    k = Nat.card (Nat.Partition a) := by
  -- classify each representative by a partition …
  have hf : ∀ i, ∃ lam : Nat.Partition a, Nonempty (rep i ≃* partitionGroup p lam) :=
    fun i => abelian_pa_classification p a (rep i) (hcard i)
  choose f hfe using hf
  -- … and realise each partition by a representative.
  have hg : ∀ lam : Nat.Partition a, ∃ i, Nonempty (partitionGroup p lam ≃* rep i) :=
    fun lam => hcomplete (partitionGroup p lam) (card_partitionGroup p lam)
  choose g hge using hg
  have left : Function.LeftInverse g f := fun i =>
    (hdistinct i (g (f i)) ⟨(hfe i).some.trans (hge (f i)).some⟩).symm
  have right : Function.RightInverse g f := fun lam =>
    ((partitionGroup_mulEquiv_iff p).mp ⟨(hge lam).some.trans (hfe (g lam)).some⟩).symm
  calc k = Nat.card (Fin k) := (Nat.card_eq_fintype_card.trans (Fintype.card_fin k)).symm
    _ = Nat.card (Nat.Partition a) := Nat.card_congr ⟨f, g, left, right⟩

end Smallgroups.UsefulTheorems
