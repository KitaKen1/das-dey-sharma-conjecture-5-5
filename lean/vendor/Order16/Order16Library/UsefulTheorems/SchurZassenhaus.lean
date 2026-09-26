/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Complement

/-!
# Schur–Zassenhaus, as a classification tool

The **Schur–Zassenhaus theorem** states that a normal subgroup `N ⊴ G` whose order is coprime to its
index has a complement. Mathlib proves this as `Subgroup.exists_right_complement'_of_coprime`
(existence of a complement) and provides `SemidirectProduct.mulEquivSubgroup` (a normal subgroup
with a complement realises `G` as a semidirect product).

For the classification project, non-abelian groups are represented as **semidirect products**
(`ℤ/p ⋊ ℤ/q`, `ℤ/p² ⋊ ℤ/p`, …), so the convenient packaging is the semidirect-product form:

* `schurZassenhaus_semidirectProduct` — a finite group with a coprime-index normal subgroup `N` is
  `G ≃* N ⋊[φ] K` for some complement `K` and conjugation action `φ`;
* `schurZassenhaus_of_card` — the same, phrased through a coprime factorisation `|G| = m * n` of the
  order with `|N| = m`.

This is the general form of the ad-hoc semidirect-product splitting used for orders `pq` and `p³`.
-/

namespace Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- **Schur–Zassenhaus (semidirect-product form).** If `G` is finite and `N` is a normal subgroup
whose order is coprime to its index, then `G` is isomorphic to a semidirect product `N ⋊[φ] K`,
where `K` is a complement of `N` and `φ` is the conjugation action of `K` on `N`. -/
theorem schurZassenhaus_semidirectProduct [Finite G] (N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ (K : Subgroup G) (φ : K →* MulAut N), Nonempty (G ≃* SemidirectProduct N K φ) := by
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hN
  exact ⟨K, _, ⟨(SemidirectProduct.mulEquivSubgroup hK).symm⟩⟩

/-- **Schur–Zassenhaus from a coprime factorisation of the order.** If `|G| = m * n` with `m`, `n`
coprime and `N` is a normal subgroup of order `m`, then `G ≃* N ⋊[φ] K` for some complement `K`
(necessarily of order `n`) and conjugation action `φ`. -/
theorem schurZassenhaus_of_card [Finite G] {m n : ℕ} (hcard : Nat.card G = m * n)
    (hcop : Nat.Coprime m n) (N : Subgroup G) [N.Normal] (hNcard : Nat.card N = m) :
    ∃ (K : Subgroup G) (φ : K →* MulAut N), Nonempty (G ≃* SemidirectProduct N K φ) := by
  apply schurZassenhaus_semidirectProduct
  have hm : 0 < m := hNcard ▸ Nat.card_pos
  have hidx : N.index = n := by
    have hmul := N.card_mul_index
    rw [hNcard, hcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hm hmul
  rw [hNcard, hidx]
  exact hcop

end Smallgroups.UsefulTheorems
