/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.PrimeOrderCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic

/-!
# Reusable engine for single-class classifications

Many small orders (`1` and every prime) have a *unique* group up to isomorphism, namely a cyclic
group.  This file provides the shared machinery the per-order files specialise:

* `CyclicRep n = Multiplicative (ZMod n)` — the cyclic group `ℤ/n` as a multiplicative group,
  used as the canonical representative.
* `card_cyclicRep` — it has order `n`.
* `cyclicRep_classification` — a cyclic group of order `n` is isomorphic to `CyclicRep n`.
* `prime_classification`, `prime_isCyclic`, `prime_unique` — the prime-order specialisations.
* `singleReps` / `singleReps_distinct` — the `Fin 1`-indexed list of representatives used to state
  the (vacuous) distinctness theorem for single-class classifications.
-/

namespace Smallgroups.UsefulTheorems

/-- The cyclic group `ℤ/n`, written multiplicatively. Canonical representative of a cyclic
isomorphism class. -/
abbrev CyclicRep (n : ℕ) : Type := Multiplicative (ZMod n)

/-- `CyclicRep n` has order `n` (for `n ≠ 0`). -/
theorem card_cyclicRep {n : ℕ} (hn : n ≠ 0) : Nat.card (CyclicRep n) = n := by
  haveI : NeZero n := ⟨hn⟩
  simp [CyclicRep, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-- **Core classification.** A cyclic group of order `n` is isomorphic to `CyclicRep n = ℤ/n`. -/
theorem cyclicRep_classification {G : Type*} [Group G] [IsCyclic G] {n : ℕ} (hn : n ≠ 0)
    (h : Nat.card G = n) : Nonempty (G ≃* CyclicRep n) :=
  ⟨mulEquivOfCyclicCardEq (h.trans (card_cyclicRep hn).symm)⟩

/-- A group of prime order is isomorphic to `CyclicRep p = ℤ/p`. -/
theorem prime_classification {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : Nat.card G = p) : Nonempty (G ≃* CyclicRep p) :=
  haveI : IsCyclic G := Smallgroups.isCyclic_of_card_eq_prime hp h
  cyclicRep_classification hp.ne_zero h

/-- A group of prime order is cyclic. -/
theorem prime_isCyclic {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (h : Nat.card G = p) :
    IsCyclic G :=
  Smallgroups.isCyclic_of_card_eq_prime hp h

/-- Any two groups of the same prime order are isomorphic. -/
theorem prime_unique {G H : Type*} [Group G] [Group H] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) (hH : Nat.card H = p) : Nonempty (G ≃* H) :=
  haveI : Fact p.Prime := ⟨hp⟩
  ⟨mulEquivOfPrimeCardEq hG hH⟩

/-! ### Distinctness scaffolding for single-class orders

When a classification has a single representative `R`, we index the representatives by `Fin 1`.
The distinctness statement "distinct representatives are non-isomorphic" is then vacuously true. -/

/-- The `Fin 1`-indexed family of representatives of a single-class classification. -/
abbrev singleReps (R : Type) : Fin 1 → Type := fun _ => R

instance instGroupSingleReps (R : Type) [Group R] (i : Fin 1) : Group (singleReps R i) :=
  inferInstanceAs (Group R)

/-- **Distinctness (vacuous).** With a single representative there are no two distinct indices, so
the representatives are pairwise non-isomorphic by default. -/
theorem singleReps_distinct (R : Type) [Group R] {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (singleReps R i ≃* singleReps R j) :=
  absurd (Subsingleton.elim i j) hij

end Smallgroups.UsefulTheorems
