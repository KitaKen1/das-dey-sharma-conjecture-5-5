/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Order16Library.UsefulTheorems.CenterInvariant
import Order16Library.UsefulTheorems.SemidirectProductClassify

/-!
# Counting isomorphism classes

This file provides the bookkeeping needed to turn an **exhaustiveness** theorem and a
**distinctness** theorem into a genuine statement about the *number* of isomorphism classes of
groups of a given order.

The number of classes of order `N` is packaged as a `Fin k`-indexed family `rep` of groups
together with the proof `IsClassif N rep` that the family is

* well-formed — each `rep i` has order `N`;
* **complete** (exhaustiveness) — every group of order `N` is isomorphic to some `rep i`;
* **non-redundant** (distinctness) — `rep i ≃* rep j` forces `i = j`.

The headline result is `IsClassif.card_unique`: **the number `k` is well defined**, i.e. any two
such lists for the same order have the same length.  Hence proving `IsClassif N rep` with
`rep : Fin k → Type` is exactly a proof that "there are exactly `k` isomorphism classes of groups
of order `N`", and it is built from the exhaustiveness and distinctness inputs.

`isClassif_one` and `isClassif_two` are the convenient constructors for the one- and two-class
cases used by the per-order files.
-/

namespace Smallgroups.UsefulTheorems

/-- `IsClassif N rep` states that the `Fin k`-indexed family of groups `rep` is a complete list of
pairwise non-isomorphic representatives of the isomorphism classes of groups of order `N`. -/
structure IsClassif (N : ℕ) {k : ℕ} (rep : Fin k → Type) [∀ i, Group (rep i)] : Prop where
  /-- Each representative is a group of order `N`. -/
  card : ∀ i, Nat.card (rep i) = N
  /-- **Exhaustiveness:** every group of order `N` is one of the representatives. -/
  complete : ∀ (G : Type) [Group G], Nat.card G = N → ∃ i, Nonempty (G ≃* rep i)
  /-- **Distinctness:** the representatives are pairwise non-isomorphic. -/
  distinct : ∀ i j, Nonempty (rep i ≃* rep j) → i = j

variable {N k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]

/-- Combining exhaustiveness and distinctness: every group of order `N` is isomorphic to a
**unique** representative. -/
theorem IsClassif.existsUnique (h : IsClassif N rep) (G : Type) [Group G] (hG : Nat.card G = N) :
    ∃! i, Nonempty (G ≃* rep i) := by
  obtain ⟨i, hi⟩ := h.complete G hG
  exact ⟨i, hi, fun j hj => h.distinct j i ⟨hj.some.symm.trans hi.some⟩⟩

/-- **The number of isomorphism classes is well defined.** Any two complete lists of pairwise
non-isomorphic representatives of the groups of order `N` have the same length. -/
theorem IsClassif.card_unique {k' : ℕ} {rep' : Fin k' → Type} [∀ i, Group (rep' i)]
    (h : IsClassif N rep) (h' : IsClassif N rep') : k = k' := by
  -- Map each representative of one list to the (unique) isomorphic representative of the other.
  let f : Fin k → Fin k' := fun i => (h'.complete (rep i) (h.card i)).choose
  let g : Fin k' → Fin k := fun j => (h.complete (rep' j) (h'.card j)).choose
  have hf : ∀ i, Nonempty (rep i ≃* rep' (f i))
  := fun i => (h'.complete (rep i) (h.card i)).choose_spec
  have hg : ∀ j, Nonempty (rep' j ≃* rep (g j))
  := fun j => (h.complete (rep' j) (h'.card j)).choose_spec
  have left : Function.LeftInverse g f := fun i =>
    (h.distinct i (g (f i)) ⟨(hf i).some.trans (hg (f i)).some⟩).symm
  have right : Function.RightInverse g f := fun j =>
    (h'.distinct j (f (g j)) ⟨(hg j).some.trans (hf (g j)).some⟩).symm
  have e : Fin k ≃ Fin k' := ⟨f, g, left, right⟩
  simpa using Fintype.card_congr e

/-! ### Constructors for the one- and two-class cases -/

/-- The one-element representative family. -/
def rep1 (A : Type) : Fin 1 → Type := fun _ => A

instance instGroupRep1 (A : Type) [Group A] : ∀ i, Group (rep1 A i) := fun _ => ‹Group A›

/-- A single representative `A` of order `N` that exhausts the groups of order `N` gives a
one-class classification. -/
theorem isClassif_one {N : ℕ} (A : Type) [Group A] (hA : Nat.card A = N)
    (hcomplete : ∀ (G : Type) [Group G], Nat.card G = N → Nonempty (G ≃* A)) :
    IsClassif N (rep1 A) where
  card _ := hA
  complete G _ hG := ⟨0, hcomplete G hG⟩
  distinct i j _ := Subsingleton.elim i j

/-- Reindexing a classification by an equivalence of the index set. -/
theorem IsClassif.of_perm {N k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif N rep) (σ : Fin k ≃ Fin k) : IsClassif N (fun i => rep (σ i)) where
  card i := h.card (σ i)
  complete G _ hG :=
    let ⟨i, hi⟩ := h.complete G hG
    ⟨σ.symm i, (σ.apply_symm_apply i).symm ▸ hi⟩
  distinct i j hiso := σ.injective (h.distinct (σ i) (σ j) hiso)

/-- Transporting a classification along pointwise isomorphisms of the representatives. -/
theorem IsClassif.of_equivs {N k : ℕ} {rep rep' : Fin k → Type} [∀ i, Group (rep i)]
    [∀ i, Group (rep' i)] (h : IsClassif N rep) (e : ∀ i, rep' i ≃* rep i) :
    IsClassif N rep' where
  card i := by
    rw [Nat.card_congr (e i).toEquiv]
    exact h.card i
  complete G _ hG :=
    let ⟨i, hi⟩ := h.complete G hG
    ⟨i, ⟨hi.some.trans (e i).symm⟩⟩
  distinct i j hiso := h.distinct i j ⟨((e i).symm.trans hiso.some).trans (e j)⟩

/-- The two-element representative family. -/
def rep2 (A B : Type) : Fin 2 → Type
  | 0 => A
  | 1 => B

instance instGroupRep2 (A B : Type) [Group A] [Group B] : ∀ i, Group (rep2 A B i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›

/-- Two representatives `A`, `B` of order `N` that together exhaust the groups of order `N` and are
not isomorphic give a two-class classification. -/
theorem isClassif_two {N : ℕ} (A B : Type) [Group A] [Group B]
    (hA : Nat.card A = N) (hB : Nat.card B = N)
    (hcomplete : ∀ (G : Type) [Group G], Nat.card G = N → Nonempty (G ≃* A) ∨ Nonempty (G ≃* B))
    (hdistinct : ¬ Nonempty (A ≃* B)) :
    IsClassif N (rep2 A B) where
  card i := by fin_cases i <;> assumption
  complete G _ hG := by
    rcases hcomplete G hG with hh | hh
    · exact ⟨0, hh⟩
    · exact ⟨1, hh⟩
  distinct i j hiso := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hiso hdistinct
    · exact absurd ⟨hiso.some.symm⟩ hdistinct
    · rfl


/-- An abelian group is never isomorphic to a non-abelian one. -/
theorem isEmpty_mulEquiv_of_comm_noncomm {A B : Type*} [Group A] [Group B]
    (hA : ∀ a b : A, a * b = b * a) (hB : ¬ ∀ a b : B, a * b = b * a) :
    ¬ Nonempty (A ≃* B) := by
  rintro ⟨f⟩
  apply hB
  intro a b
  have h := hA (f.symm a) (f.symm b)
  calc a * b = f (f.symm a * f.symm b) := by simp
    _ = f (f.symm b * f.symm a) := by rw [h]
    _ = b * a := by simp

/-- The three-element representative family. -/
def rep3 (A B C : Type) : Fin 3 → Type
  | 0 => A
  | 1 => B
  | 2 => C

instance instGroupRep3 (A B C : Type) [Group A] [Group B] [Group C] : ∀ i, Group (rep3 A B C i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›

/-! ### Constructor for the three-class case -/

/-- Three representatives of order `N` that together
exhaust the groups of order `N` and are pairwise
non-isomorphic give a three-class classification. -/
theorem isClassif_three {N : ℕ} (A B C : Type) [Group A] [Group B] [Group C]
    (hA : Nat.card A = N) (hB : Nat.card B = N) (hC : Nat.card C = N)
    (hcomplete : ∀ (G : Type) [Group G], Nat.card G = N →
      Nonempty (G ≃* A) ∨ Nonempty (G ≃* B) ∨ Nonempty (G ≃* C))
    (hAB : ¬ Nonempty (A ≃* B)) (hAC : ¬ Nonempty (A ≃* C))
    (hBC : ¬ Nonempty (B ≃* C)) :
    IsClassif N (rep3 A B C) where
  card i := by fin_cases i <;> assumption
  complete G _ hG := by
    rcases hcomplete G hG with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  distinct i j hiso := by
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hiso ‹_›
        | exact absurd (Nonempty.intro hiso.some.symm) ‹_›

/-! ### Constructor for the four-class case -/

/-- The four-element representative family. -/
def rep4 (A B C D : Type) : Fin 4 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D

instance instGroupRep4 (A B C D : Type) [Group A] [Group B] [Group C] [Group D] :
    ∀ i, Group (rep4 A B C D i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›

/-- Four representatives of order `N` that together exhaust the groups of order `N` and are pairwise
non-isomorphic give a four-class classification. -/
theorem isClassif_four {N : ℕ} (A B C D : Type)
    [Group A] [Group B] [Group C] [Group D]
    (hA : Nat.card A = N) (hB : Nat.card B = N) (hC : Nat.card C = N) (hD : Nat.card D = N)
    (hcomplete : ∀ (G : Type) [Group G], Nat.card G = N → Nonempty (G ≃* A) ∨ Nonempty (G ≃* B) ∨
      Nonempty (G ≃* C) ∨ Nonempty (G ≃* D))
    (hAB : ¬ Nonempty (A ≃* B)) (hAC : ¬ Nonempty (A ≃* C)) (hAD : ¬ Nonempty (A ≃* D))
    (hBC : ¬ Nonempty (B ≃* C)) (hBD : ¬ Nonempty (B ≃* D))
    (hCD : ¬ Nonempty (C ≃* D)) :
    IsClassif N (rep4 A B C D) where
  card i := by fin_cases i <;> assumption
  complete G _ hG := by
    rcases hcomplete G hG with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
  distinct i j hiso := by
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hiso ‹_›
        | exact absurd (Nonempty.intro hiso.some.symm) ‹_›

/-! ### Constructor for the five-class case (used for orders `p³`) -/

/-- The five-element representative family. -/
def rep5 (A B C D E : Type) : Fin 5 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E

instance instGroupRep5 (A B C D E : Type) [Group A] [Group B] [Group C] [Group D] [Group E] :
    ∀ i, Group (rep5 A B C D E i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›
  | 4 => ‹Group E›

/-- Five representatives of order `N` that together exhaust the groups of order `N` and are pairwise
non-isomorphic give a five-class classification. -/
theorem isClassif_five {N : ℕ} (A B C D E : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E]
    (hA : Nat.card A = N) (hB : Nat.card B = N) (hC : Nat.card C = N) (hD : Nat.card D = N)
    (hE : Nat.card E = N)
    (hcomplete : ∀ (G : Type) [Group G], Nat.card G = N → Nonempty (G ≃* A) ∨ Nonempty (G ≃* B) ∨
      Nonempty (G ≃* C) ∨ Nonempty (G ≃* D) ∨ Nonempty (G ≃* E))
    (hAB : ¬ Nonempty (A ≃* B)) (hAC : ¬ Nonempty (A ≃* C)) (hAD : ¬ Nonempty (A ≃* D))
    (hAE : ¬ Nonempty (A ≃* E)) (hBC : ¬ Nonempty (B ≃* C)) (hBD : ¬ Nonempty (B ≃* D))
    (hBE : ¬ Nonempty (B ≃* E)) (hCD : ¬ Nonempty (C ≃* D)) (hCE : ¬ Nonempty (C ≃* E))
    (hDE : ¬ Nonempty (D ≃* E)) :
    IsClassif N (rep5 A B C D E) where
  card i := by fin_cases i <;> assumption
  complete G _ hG := by
    rcases hcomplete G hG with h | h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩]
  distinct i j hiso := by
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hiso ‹_›
        | exact absurd (Nonempty.intro hiso.some.symm) ‹_›

/-! ### Combining pairwise non-isomorphic families

Rather than checking every cross pair when a list of representatives splits into groups (e.g. the
abelian ones and the non-abelian ones), prove each group is internally pairwise non-isomorphic and
that the groups are disjoint, then concatenate. -/

/-- A family of groups is pairwise non-isomorphic. This is exactly the `distinct` field of
`IsClassif`. -/
def PairwiseNonMulEquiv {ι : Type*} (rep : ι → Type) [∀ i, Group (rep i)] : Prop :=
  ∀ i j, Nonempty (rep i ≃* rep j) → i = j

/-- A complete classification must have at least as many representatives as any pairwise
non-isomorphic family of known groups of the same order. -/
theorem IsClassif.card_ge_of_pairwise {m : ℕ} {known : Fin m → Type} [∀ i, Group (known i)]
    (h : IsClassif N rep) (hcard : ∀ i, Nat.card (known i) = N)
    (hdistinct : PairwiseNonMulEquiv known) : m ≤ k := by
  let f : Fin m → Fin k := fun i => (h.complete (known i) (hcard i)).choose
  have hfiso : ∀ i, Nonempty (known i ≃* rep (f i)) := fun i =>
    (h.complete (known i) (hcard i)).choose_spec
  have hinj : Function.Injective f := by
    intro i j hf
    exact hdistinct i j
      ⟨(hfiso i).some.trans ((MulEquiv.cast hf).trans (hfiso j).some.symm)⟩
  simpa using Fintype.card_le_of_injective f hinj

/-- The `Sum.elim` of two families of groups is again a family of groups. -/
instance instGroupSumElim {ι κ : Type*} {A : ι → Type} {B : κ → Type}
    [∀ i, Group (A i)] [∀ j, Group (B j)] : ∀ s : ι ⊕ κ, Group (Sum.elim A B s)
  | Sum.inl i => inferInstanceAs (Group (A i))
  | Sum.inr j => inferInstanceAs (Group (B j))

/-- **Concatenating two disjoint pairwise-non-isomorphic families.** If `A` and `B` are each
pairwise non-isomorphic and no `A i` is isomorphic to any `B j`, then `Sum.elim A B` is pairwise
non-isomorphic. -/
theorem PairwiseNonMulEquiv.sum {ι κ : Type*} {A : ι → Type} {B : κ → Type}
    [∀ i, Group (A i)] [∀ j, Group (B j)]
    (hA : PairwiseNonMulEquiv A) (hB : PairwiseNonMulEquiv B)
    (hdisj : ∀ i j, ¬ Nonempty (A i ≃* B j)) :
    PairwiseNonMulEquiv (Sum.elim A B) := by
  rintro (i | i) (j | j) ⟨e⟩
  · exact congrArg Sum.inl (hA i j ⟨e⟩)
  · exact absurd ⟨e⟩ (hdisj i j)
  · exact absurd ⟨e.symm⟩ (hdisj j i)
  · exact congrArg Sum.inr (hB i j ⟨e⟩)

/-- Reindex a pairwise-non-isomorphic family along an equivalence of the index. -/
theorem PairwiseNonMulEquiv.reindex {ι κ : Type*} {rep : ι → Type} [∀ i, Group (rep i)]
    (e : κ ≃ ι) (h : PairwiseNonMulEquiv rep) :
    PairwiseNonMulEquiv (fun k => rep (e k)) :=
  fun i j hiso => e.injective (h (e i) (e j) hiso)

/-! ### Constructor for the six-class case (used for orders `2pq` with `p ∣ q - 1`) -/

/-- The six-element representative family. -/
def rep6 (A B C D E F : Type) : Fin 6 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E
  | 5 => F

instance instGroupRep6 (A B C D E F : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F] :
    ∀ i, Group (rep6 A B C D E F i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›
  | 4 => ‹Group E›
  | 5 => ‹Group F›

/-- Six representatives of order `N` that together exhaust the groups of order `N` and are pairwise
non-isomorphic give a six-class classification. -/
theorem isClassif_six {N : ℕ} (A B C D E F : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F]
    (hA : Nat.card A = N) (hB : Nat.card B = N) (hC : Nat.card C = N) (hD : Nat.card D = N)
    (hE : Nat.card E = N) (hF : Nat.card F = N)
    (hcomplete : ∀ (G : Type) [Group G], Nat.card G = N → Nonempty (G ≃* A) ∨ Nonempty (G ≃* B) ∨
      Nonempty (G ≃* C) ∨ Nonempty (G ≃* D) ∨ Nonempty (G ≃* E) ∨ Nonempty (G ≃* F))
    (hAB : ¬ Nonempty (A ≃* B)) (hAC : ¬ Nonempty (A ≃* C)) (hAD : ¬ Nonempty (A ≃* D))
    (hAE : ¬ Nonempty (A ≃* E)) (hAF : ¬ Nonempty (A ≃* F))
    (hBC : ¬ Nonempty (B ≃* C)) (hBD : ¬ Nonempty (B ≃* D))
    (hBE : ¬ Nonempty (B ≃* E)) (hBF : ¬ Nonempty (B ≃* F))
    (hCD : ¬ Nonempty (C ≃* D)) (hCE : ¬ Nonempty (C ≃* E)) (hCF : ¬ Nonempty (C ≃* F))
    (hDE : ¬ Nonempty (D ≃* E)) (hDF : ¬ Nonempty (D ≃* F))
    (hEF : ¬ Nonempty (E ≃* F)) :
    IsClassif N (rep6 A B C D E F) where
  card i := by fin_cases i <;> assumption
  complete G _ hG := by
    rcases hcomplete G hG with h | h | h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩]
  distinct i j hiso := by
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hiso ‹_›
        | exact absurd (Nonempty.intro hiso.some.symm) ‹_›

/-- The seven-element representative family. -/
def rep7 (A B C D E F G : Type) : Fin 7 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E
  | 5 => F
  | 6 => G

instance instGroupRep7 (A B C D E F G : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F] [Group G] :
    ∀ i, Group (rep7 A B C D E F G i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›
  | 4 => ‹Group E›
  | 5 => ‹Group F›
  | 6 => ‹Group G›

/-- The eight-element representative family. -/
def rep8 (A B C D E F G H : Type) : Fin 8 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E
  | 5 => F
  | 6 => G
  | 7 => H

instance instGroupRep8 (A B C D E F G H : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F] [Group G] [Group H] :
    ∀ i, Group (rep8 A B C D E F G H i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›
  | 4 => ‹Group E›
  | 5 => ‹Group F›
  | 6 => ‹Group G›
  | 7 => ‹Group H›

/-- The nine-element representative family. -/
def rep9 (A B C D E F G H I : Type) : Fin 9 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E
  | 5 => F
  | 6 => G
  | 7 => H
  | 8 => I

instance instGroupRep9 (A B C D E F G H I : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F] [Group G] [Group H]
    [Group I] :
    ∀ i, Group (rep9 A B C D E F G H I i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›
  | 4 => ‹Group E›
  | 5 => ‹Group F›
  | 6 => ‹Group G›
  | 7 => ‹Group H›
  | 8 => ‹Group I›

/-- The twelve-element representative family. -/
def rep12 (A B C D E F G H I J K L : Type) : Fin 12 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E
  | 5 => F
  | 6 => G
  | 7 => H
  | 8 => I
  | 9 => J
  | 10 => K
  | 11 => L

instance instGroupRep12 (A B C D E F G H I J K L : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F]
    [Group G] [Group H] [Group I] [Group J] [Group K] [Group L] :
    ∀ i, Group (rep12 A B C D E F G H I J K L i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›
  | 4 => ‹Group E›
  | 5 => ‹Group F›
  | 6 => ‹Group G›
  | 7 => ‹Group H›
  | 8 => ‹Group I›
  | 9 => ‹Group J›
  | 10 => ‹Group K›
  | 11 => ‹Group L›

/-- Twelve representatives of order `N` that together exhaust the groups of order `N` and are
pairwise non-isomorphic give a twelve-class classification. -/
theorem isClassif_twelve {N : ℕ} (A B C D E F G H I J K L : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F]
    [Group G] [Group H] [Group I] [Group J] [Group K] [Group L]
    (hA : Nat.card A = N) (hB : Nat.card B = N) (hC : Nat.card C = N)
    (hD : Nat.card D = N) (hE : Nat.card E = N) (hF : Nat.card F = N)
    (hG : Nat.card G = N) (hH : Nat.card H = N) (hI : Nat.card I = N)
    (hJ : Nat.card J = N) (hK : Nat.card K = N) (hL : Nat.card L = N)
    (hcomplete : ∀ (X : Type) [Group X], Nat.card X = N →
      Nonempty (X ≃* A) ∨ Nonempty (X ≃* B) ∨ Nonempty (X ≃* C) ∨
        Nonempty (X ≃* D) ∨ Nonempty (X ≃* E) ∨ Nonempty (X ≃* F) ∨
        Nonempty (X ≃* G) ∨ Nonempty (X ≃* H) ∨ Nonempty (X ≃* I) ∨
        Nonempty (X ≃* J) ∨ Nonempty (X ≃* K) ∨ Nonempty (X ≃* L))
    (hdistinct : PairwiseNonMulEquiv (rep12 A B C D E F G H I J K L)) :
    IsClassif N (rep12 A B C D E F G H I J K L) where
  card i := by fin_cases i <;> assumption
  complete X _ hX := by
    rcases hcomplete X hX with h | h | h | h | h | h | h | h | h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩,
      ⟨6, h⟩, ⟨7, h⟩, ⟨8, h⟩, ⟨9, h⟩, ⟨10, h⟩, ⟨11, h⟩]
  distinct i j hiso := hdistinct i j hiso

/-- The thirteen-element representative family. -/
def rep13 (A B C D E F G H I J K L M : Type) : Fin 13 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E
  | 5 => F
  | 6 => G
  | 7 => H
  | 8 => I
  | 9 => J
  | 10 => K
  | 11 => L
  | 12 => M

instance instGroupRep13 (A B C D E F G H I J K L M : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F]
    [Group G] [Group H] [Group I] [Group J] [Group K] [Group L] [Group M] :
    ∀ i, Group (rep13 A B C D E F G H I J K L M i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›
  | 4 => ‹Group E›
  | 5 => ‹Group F›
  | 6 => ‹Group G›
  | 7 => ‹Group H›
  | 8 => ‹Group I›
  | 9 => ‹Group J›
  | 10 => ‹Group K›
  | 11 => ‹Group L›
  | 12 => ‹Group M›

/-- The fourteen-element representative family. -/
def rep14 (A B C D E F G H I J K L M N' : Type) : Fin 14 → Type
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E
  | 5 => F
  | 6 => G
  | 7 => H
  | 8 => I
  | 9 => J
  | 10 => K
  | 11 => L
  | 12 => M
  | 13 => N'

instance instGroupRep14 (A B C D E F G H I J K L M N' : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F]
    [Group G] [Group H] [Group I] [Group J] [Group K] [Group L] [Group M] [Group N'] :
    ∀ i, Group (rep14 A B C D E F G H I J K L M N' i)
  | 0 => ‹Group A›
  | 1 => ‹Group B›
  | 2 => ‹Group C›
  | 3 => ‹Group D›
  | 4 => ‹Group E›
  | 5 => ‹Group F›
  | 6 => ‹Group G›
  | 7 => ‹Group H›
  | 8 => ‹Group I›
  | 9 => ‹Group J›
  | 10 => ‹Group K›
  | 11 => ‹Group L›
  | 12 => ‹Group M›
  | 13 => ‹Group N'›

/-- Thirteen representatives of order `N` that together exhaust the groups of order `N` and are
pairwise non-isomorphic give a thirteen-class classification. -/
theorem isClassif_thirteen {N : ℕ} (A B C D E F G H I J K L M : Type)
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F]
    [Group G] [Group H] [Group I] [Group J] [Group K] [Group L] [Group M]
    (hA : Nat.card A = N) (hB : Nat.card B = N) (hC : Nat.card C = N)
    (hD : Nat.card D = N) (hE : Nat.card E = N) (hF : Nat.card F = N)
    (hG : Nat.card G = N) (hH : Nat.card H = N) (hI : Nat.card I = N)
    (hJ : Nat.card J = N) (hK : Nat.card K = N) (hL : Nat.card L = N) (hM : Nat.card M = N)
    (hcomplete : ∀ (X : Type) [Group X], Nat.card X = N →
      Nonempty (X ≃* A) ∨ Nonempty (X ≃* B) ∨ Nonempty (X ≃* C) ∨
        Nonempty (X ≃* D) ∨ Nonempty (X ≃* E) ∨ Nonempty (X ≃* F) ∨
        Nonempty (X ≃* G) ∨ Nonempty (X ≃* H) ∨ Nonempty (X ≃* I) ∨
        Nonempty (X ≃* J) ∨ Nonempty (X ≃* K) ∨ Nonempty (X ≃* L) ∨ Nonempty (X ≃* M))
    (hdistinct : PairwiseNonMulEquiv (rep13 A B C D E F G H I J K L M)) :
    IsClassif N (rep13 A B C D E F G H I J K L M) where
  card i := by fin_cases i <;> assumption
  complete X _ hX := by
    rcases hcomplete X hX with h | h | h | h | h | h | h | h | h | h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩,
      ⟨6, h⟩, ⟨7, h⟩, ⟨8, h⟩, ⟨9, h⟩, ⟨10, h⟩, ⟨11, h⟩, ⟨12, h⟩]
  distinct i j hiso := hdistinct i j hiso

/-- **Abelian and non-abelian families are disjoint.** Supplies the disjointness hypothesis of
`PairwiseNonMulEquiv.sum` when every `A i` is commutative and every `B j` is not. -/
theorem pairwise_disjoint_of_comm_noncomm {ι κ : Type*} {A : ι → Type} {B : κ → Type}
    [∀ i, Group (A i)] [∀ j, Group (B j)]
    (hA : ∀ i, ∀ a b : A i, a * b = b * a) (hB : ∀ j, ¬ ∀ a b : B j, a * b = b * a) :
    ∀ i j, ¬ Nonempty (A i ≃* B j) :=
  fun i j => isEmpty_mulEquiv_of_comm_noncomm (hA i) (hB j)

/-- **Combining distinct abelian and distinct non-abelian families.** If `A` is a pairwise
non-isomorphic family of abelian groups and `B` is a pairwise non-isomorphic family of non-abelian
groups, then `Sum.elim A B` is pairwise non-isomorphic. -/
theorem PairwiseNonMulEquiv.sum_of_comm_noncomm {ι κ : Type*} {A : ι → Type} {B : κ → Type}
    [∀ i, Group (A i)] [∀ j, Group (B j)]
    (hA : PairwiseNonMulEquiv A) (hB : PairwiseNonMulEquiv B)
    (hAcomm : ∀ i, ∀ a b : A i, a * b = b * a)
    (hBnoncomm : ∀ j, ¬ ∀ a b : B j, a * b = b * a) :
    PairwiseNonMulEquiv (Sum.elim A B) :=
  hA.sum hB (pairwise_disjoint_of_comm_noncomm hAcomm hBnoncomm)

/-! ### Partition-based distinctness

When a family of representatives can be partitioned by a group invariant (e.g. commutativity,
center cardinality), it suffices to prove pairwise non-isomorphism *within* each part. The
invariant handles all cross-part pairs automatically.

The master theorem is `PairwiseNonMulEquiv.of_invariant`: given any function `inv : ι → α` that
is preserved by isomorphisms (`rep i ≃* rep j → inv i = inv j`), distinctness reduces to checking
pairs with the same `inv`-value. -/

/-- **Partition by invariant.** If `inv` is a group-isomorphism invariant on the index and each
fiber of `inv` is pairwise non-isomorphic, then the whole family is pairwise non-isomorphic.

Use this to reduce `C(n,2)` distinctness checks to the sum of `C(nᵢ,2)` within each invariant
class. Typical invariants: commutativity, center cardinality, abelianization size. -/
theorem PairwiseNonMulEquiv.of_invariant {ι : Type*} {rep : ι → Type}
    [∀ i, Group (rep i)] {α : Type*}
    (inv : ι → α)
    (hinv : ∀ i j, Nonempty (rep i ≃* rep j) → inv i = inv j)
    (hfiber : ∀ i j, inv i = inv j → Nonempty (rep i ≃* rep j) → i = j) :
    PairwiseNonMulEquiv rep :=
  fun i j h => hfiber i j (hinv i j h) h

/-- **Multi-way sum via invariant.** Concatenate arbitrarily many internally-distinct families
indexed by `Sigma`, where families with different `a`-indices are guaranteed non-isomorphic by an
invariant. -/
theorem PairwiseNonMulEquiv.sigma {α : Type*} {ι : α → Type*}
    {rep : (a : α) → ι a → Type}
    [∀ a i, Group (rep a i)]
    (hparts : ∀ a, PairwiseNonMulEquiv (rep a))
    (hdisj : ∀ a₁ a₂, a₁ ≠ a₂ → ∀ i j,
      ¬ Nonempty (rep a₁ i ≃* rep a₂ j)) :
    PairwiseNonMulEquiv (fun (s : Σ a, ι a) => rep s.1 s.2) := by
  rintro ⟨a₁, i₁⟩ ⟨a₂, i₂⟩ ⟨e⟩
  by_cases h : a₁ = a₂
  · subst h
    exact congrArg (Sigma.mk a₁) (hparts a₁ i₁ i₂ ⟨e⟩)
  · exact absurd ⟨e⟩ (hdisj a₁ a₂ h i₁ i₂)

/-! ### Center-cardinality specialisations

The center cardinality `|Z(G)|` is a group-isomorphism invariant. Combining this fact with the
generic `of_invariant` and `sigma` theorems gives ready-to-use distinctness tools that only require:

* a center-size map `cs : ι → ℕ` with proofs that each `rep i` has center of size `cs i`, and
* within-fiber distinctness for indices that share the same center size. -/

/-- **Partition by center cardinality.** Specialises `of_invariant` with `|Z(−)|` as the
invariant. Most pairs are separated by having different center sizes; only pairs sharing a center
size need an explicit non-isomorphism proof (the `hfiber` hypothesis). -/
theorem PairwiseNonMulEquiv.of_center_card {ι : Type*} {rep : ι → Type}
    [∀ i, Group (rep i)]
    (cs : ι → ℕ)
    (hc : ∀ i, Nat.card (Subgroup.center (rep i)) = cs i)
    (hfiber : ∀ i j, cs i = cs j → Nonempty (rep i ≃* rep j) → i = j) :
    PairwiseNonMulEquiv rep :=
  PairwiseNonMulEquiv.of_invariant cs
    (fun i j ⟨e⟩ => by rw [← hc i, ← hc j]; exact card_center_eq_of_mulEquiv e)
    hfiber

/-- **Multi-way sum by center cardinality.** Specialises `sigma` using `|Z(−)|` to prove
cross-family disjointness. Each family is internally pairwise non-isomorphic, and families at
different `α`-indices have provably different center sizes, so no cross-family pair can be
isomorphic. -/
theorem PairwiseNonMulEquiv.sigma_of_center_card {α : Type*} {ι : α → Type*}
    {rep : (a : α) → ι a → Type}
    [∀ a i, Group (rep a i)]
    (cs : (a : α) → ι a → ℕ)
    (hc : ∀ a i, Nat.card (Subgroup.center (rep a i)) = cs a i)
    (hparts : ∀ a, PairwiseNonMulEquiv (rep a))
    (hdisj : ∀ a₁ a₂, a₁ ≠ a₂ → ∀ i j, cs a₁ i ≠ cs a₂ j) :
    PairwiseNonMulEquiv (fun (s : Σ a, ι a) => rep s.1 s.2) :=
  PairwiseNonMulEquiv.sigma hparts
    (fun a₁ a₂ hne i j =>
      pairwise_disjoint_of_card_center_ne
        (cs a₁) (cs a₂) (fun k => hc a₁ k) (fun k => hc a₂ k) (hdisj a₁ a₂ hne) i j)

/-! ### Semidirect-product specialisation

When every representative in a family is a semidirect product `N ⋊[φᵢ] Hᵢ` of the *same* `N`
(with `Nat.card N` coprime to each `Nat.card Hᵢ` — the hypothesis that makes `N`'s copy
characteristic in every case, via `Subgroup.characteristic_of_coprime_index`), the representatives
inherit distinctness from the `Hᵢ`: different `H`'s force different total groups. This reduces
distinctness of the semidirect products to distinctness of the (typically much smaller)
complements. -/

/-- **Partition-based distinctness for coprime-order semidirect products.** If each `rep i` is a
semidirect product `N ⋊[φ i] (H i)` of a *fixed* `N`, with `Nat.card N` coprime to `Nat.card (H i)`
for every `i`, then pairwise non-isomorphism of the `H i` implies pairwise non-isomorphism of the
`rep i`. -/
theorem PairwiseNonMulEquiv.of_semidirectProduct {ι : Type*} {N : Type*} [Group N] [Finite N]
    {H : ι → Type} [∀ i, Group (H i)] [∀ i, Finite (H i)] {φ : ∀ i, H i →* MulAut N}
    {rep : ι → Type} [∀ i, Group (rep i)]
    (e : ∀ i, Nonempty (rep i ≃* SemidirectProduct N (H i) (φ i)))
    (hcop : ∀ i, Nat.Coprime (Nat.card N) (Nat.card (H i)))
    (hH : PairwiseNonMulEquiv H) :
    PairwiseNonMulEquiv rep := by
  intro i j ⟨eij⟩
  obtain ⟨ei⟩ := e i
  obtain ⟨ej⟩ := e j
  have f : SemidirectProduct N (H i) (φ i) ≃* SemidirectProduct N (H j) (φ j) :=
    ei.symm.trans (eij.trans ej)
  exact hH i j (semidirectProduct_congr_range (hcop j) f)

end Smallgroups.UsefulTheorems
