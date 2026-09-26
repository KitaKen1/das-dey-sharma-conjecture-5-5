/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Center cardinality as a group invariant

The cardinality of the center `Z(G)` is preserved by group isomorphisms. Groups with different
center cardinalities are non-isomorphic. This gives a simple and widely applicable distinctness
tool for classification.

## Main results

* `card_center_eq_of_mulEquiv` — center cardinality is an isomorphism invariant
* `not_nonempty_mulEquiv_of_card_center_ne` — different center sizes ⇒ non-isomorphic
* `not_nonempty_mulEquiv_of_center_not_mulEquiv` — non-isomorphic centers ⇒ non-isomorphic groups
* `pairwise_disjoint_of_card_center_ne` — disjointness by center cardinality
* `pairwise_disjoint_of_center_not_iso` — disjointness by center isomorphism class
* `card_center_eq_card_of_comm` — center of a commutative group equals the whole group
* `card_center_prod` — `|Z(G × H)| = |Z(G)| · |Z(H)|`
* `card_center_bot` — `|Z(G)| = 1` when the center is trivial
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

/-- The center cardinality is preserved by group isomorphisms. -/
theorem card_center_eq_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    Nat.card (center H) = Nat.card (center K) :=
  Nat.card_congr (centerCongr e).toEquiv

/-- Groups with different center cardinalities are non-isomorphic. -/
theorem not_nonempty_mulEquiv_of_card_center_ne {H K : Type*} [Group H] [Group K]
    (h : Nat.card (center H) ≠ Nat.card (center K)) :
    ¬ Nonempty (H ≃* K) := by
  rintro ⟨e⟩
  exact h (card_center_eq_of_mulEquiv e)

/-- The center of a commutative group is the whole group. -/
theorem card_center_eq_card_of_comm (H : Type*) [Group H] (hcomm : ∀ a b : H, a * b = b * a) :
    Nat.card (center H) = Nat.card H := by
  have : center H = ⊤ := by
    rw [eq_top_iff']; intro x; rw [mem_center_iff]; intro g; exact hcomm g x
  rw [this, Subgroup.card_top]

/-- The center of a product is the product of the centers. -/
theorem card_center_prod (H K : Type*) [Group H] [Group K] :
    Nat.card (center (H × K)) =
      Nat.card (center H) * Nat.card (center K) := by
  rw [Subgroup.center_prod,
    Nat.card_congr (Subgroup.prodEquiv (center H) (center K)).toEquiv,
    Nat.card_prod]

/-- When the center is trivial, its cardinality is `1`. -/
theorem card_center_of_eq_bot {G : Type*} [Group G] (h : center G = ⊥) :
    Nat.card (center G) = 1 := by
  rw [h, Subgroup.card_bot]

/-- Groups with different center cardinalities are in disjoint invariant classes.
    Supplies the `hdisj` hypothesis of `PairwiseNonMulEquiv.sigma` or
    the `hinv` hypothesis of `PairwiseNonMulEquiv.of_invariant`. -/
theorem pairwise_disjoint_of_card_center_ne {ι κ : Type*} {A : ι → Type}
    {B : κ → Type} [∀ i, Group (A i)] [∀ j, Group (B j)]
    (cA : ι → ℕ) (cB : κ → ℕ)
    (hA : ∀ i, Nat.card (Subgroup.center (A i)) = cA i)
    (hB : ∀ j, Nat.card (Subgroup.center (B j)) = cB j)
    (hne : ∀ i j, cA i ≠ cB j) :
    ∀ i j, ¬ Nonempty (A i ≃* B j) :=
  fun i j => not_nonempty_mulEquiv_of_card_center_ne (by rw [hA, hB]; exact hne i j)

/-- Groups whose centers are non-isomorphic are themselves non-isomorphic.
    The center, as a group up to isomorphism, is an invariant of the group. -/
theorem not_nonempty_mulEquiv_of_center_not_mulEquiv {H K : Type*} [Group H] [Group K]
    (h : ¬ Nonempty (Subgroup.center H ≃* Subgroup.center K)) :
    ¬ Nonempty (H ≃* K) := by
  rintro ⟨e⟩
  apply h
  exact ⟨centerCongr e⟩

/-- Groups whose centers are non-isomorphic are in disjoint invariant classes.
    Supplies the `hdisj` hypothesis of `PairwiseNonMulEquiv.sigma` or
    the `hinv` hypothesis of `PairwiseNonMulEquiv.of_invariant`. -/
theorem pairwise_disjoint_of_center_not_iso {ι κ : Type*} {A : ι → Type}
    {B : κ → Type} [∀ i, Group (A i)] [∀ j, Group (B j)]
    (hne : ∀ i j, ¬ Nonempty (Subgroup.center (A i) ≃* Subgroup.center (B j))) :
    ∀ i j, ¬ Nonempty (A i ≃* B j) :=
  fun i j => not_nonempty_mulEquiv_of_center_not_mulEquiv (hne i j)

/-- **The center of a nontrivial finite p-group is nontrivial.**
If `G` is a finite group whose order is `p ^ n` with `0 < n` and `p` prime, then the center
`Z(G)` contains more than one element (i.e. there exists a nontrivial central element). -/
theorem center_nontrivial_of_card_prime_pow {G : Type*} [Group G] [Finite G] {p n : ℕ}
    [Fact p.Prime] (hcard : Nat.card G = p ^ n) (hn : 0 < n) :
    Nontrivial (Subgroup.center G) := by
  have hG : IsPGroup p G := IsPGroup.of_card hcard
  haveI : Nontrivial G := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow hn.ne' (Fact.out (p := p.Prime)).one_lt
  exact hG.center_nontrivial

/-- A finite group is abelian iff its center is the whole group. -/
theorem center_eq_top_iff {G : Type*} [Group G] :
    Subgroup.center G = ⊤ ↔ (∀ a b : G, a * b = b * a) := by
  constructor
  · intro h a b
    have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    rw [Subgroup.mem_center_iff] at ha
    exact (ha b).symm
  · intro hcomm
    rw [Subgroup.eq_top_iff']
    intro a
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcomm g a

/-- A finite group is abelian iff the cardinality of its center equals the cardinality of the
whole group. -/
theorem card_center_eq_card_iff {G : Type*} [Group G] [Finite G] :
    Nat.card (Subgroup.center G) = Nat.card G ↔ (∀ a b : G, a * b = b * a) := by
  constructor
  · intro h
    have h_top : Subgroup.center G = ⊤ := Subgroup.eq_top_of_card_eq _ h
    exact center_eq_top_iff.mp h_top
  · exact card_center_eq_card_of_comm G

/-- If the quotient of a group by its center is cyclic, then the group is abelian.  In particular,
the quotient by the center of a non-abelian group cannot be a nontrivial cyclic group. -/
theorem comm_of_cyclic_center_quotient {G : Type*} [Group G]
    [IsCyclic (G ⧸ Subgroup.center G)] (a b : G) : a * b = b * a := by
  letI : CommGroup G := commGroupOfCyclicCenterQuotient
    (QuotientGroup.mk' (Subgroup.center G))
    (by rw [QuotientGroup.ker_mk'])
  exact mul_comm a b

end Smallgroups.UsefulTheorems
