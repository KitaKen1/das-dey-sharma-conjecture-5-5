/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.AbelianPa
import Order16Library.UsefulTheorems.AbelianPaUniqueness

/-!
# Abelian groups of order `p^4`

The structure theorem for finite abelian groups reduces the classification of abelian groups
of order `p^4` (for any prime `p`) to the **integer partitions of `4`**.  The five partitions

  `4`, `3+1`, `2+2`, `2+1+1`, `1+1+1+1`

correspond to the five abelian groups:

  `C_{p^4}`, `C_{p^3} × C_p`, `C_{p^2} × C_{p^2}`, `C_{p^2} × C_p × C_p`, `(C_p)^4`.

In particular, this file simultaneously handles the abelian part of order `16` (`p = 2`) and
order `81` (`p = 3`).

This file records the five representatives, proves they have order `p^4`, that every abelian
group of order `p^4` is isomorphic to one of them, and that they are pairwise non-isomorphic.
-/

namespace Smallgroups.UsefulTheorems

open scoped BigOperators

/-! ### The five partitions of `4` -/

/-- Partition `4` → `C_{p^4}`. -/
def part4 : Nat.Partition 4 :=
  ⟨{4}, by intro x hx; simp at hx; omega, by simp⟩

/-- Partition `3+1` → `C_{p^3} × C_p`. -/
def part31 : Nat.Partition 4 :=
  ⟨{3, 1}, by intro x hx; simp at hx; omega, by simp⟩

/-- Partition `2+2` → `C_{p^2} × C_{p^2}`. -/
def part22 : Nat.Partition 4 :=
  ⟨{2, 2}, by intro x hx; simp at hx; omega, by simp⟩

/-- Partition `2+1+1` → `C_{p^2} × C_p × C_p`. -/
def part211 : Nat.Partition 4 :=
  ⟨{2, 1, 1}, by intro x hx; simp at hx; omega, by simp⟩

/-- Partition `1+1+1+1` → `(C_p)^4`. -/
def part1111 : Nat.Partition 4 :=
  ⟨{1, 1, 1, 1}, by intro x hx; simp at hx; omega, by simp⟩

/-! ### Map from `Fin 5` to partitions -/

/-- Map a `Fin 5` index to the corresponding partition of `4`. -/
def idxToPartition : Fin 5 → Nat.Partition 4
  | 0 => part4
  | 1 => part31
  | 2 => part22
  | 3 => part211
  | 4 => part1111

lemma idxToPartition_injective : Function.Injective idxToPartition := by
  decide +kernel

/-! ### The five abelian representatives of order `p^4` -/

/-- The five-element representative family: `partitionGroup p` applied to each partition. -/
noncomputable abbrev orderP4Abel_reps (p : ℕ) (i : Fin 5) : Type :=
  partitionGroup p (idxToPartition i)

noncomputable instance instCommGroupOrderP4AbelRep (p : ℕ) (i : Fin 5) :
    CommGroup (orderP4Abel_reps p i) := inferInstance

/-! ### Named abbreviations for the five representatives (generic `p`) -/

/-- `C_{p^4}`. -/
noncomputable abbrev orderP4Abel_A1 (p : ℕ) : Type := orderP4Abel_reps p 0

/-- `C_{p^3} × C_p`. -/
noncomputable abbrev orderP4Abel_A2 (p : ℕ) : Type := orderP4Abel_reps p 1

/-- `C_{p^2} × C_{p^2}`. -/
noncomputable abbrev orderP4Abel_A3 (p : ℕ) : Type := orderP4Abel_reps p 2

/-- `C_{p^2} × C_p × C_p`. -/
noncomputable abbrev orderP4Abel_A4 (p : ℕ) : Type := orderP4Abel_reps p 3

/-- `(C_p)^4`. -/
noncomputable abbrev orderP4Abel_A5 (p : ℕ) : Type := orderP4Abel_reps p 4

/-! ### Named representatives for order `16` (p = 2) -/

noncomputable abbrev order16_A1 : Type := orderP4Abel_A1 2
noncomputable abbrev order16_A2 : Type := orderP4Abel_A2 2
noncomputable abbrev order16_A3 : Type := orderP4Abel_A3 2
noncomputable abbrev order16_A4 : Type := orderP4Abel_A4 2
noncomputable abbrev order16_A5 : Type := orderP4Abel_A5 2

/-! ### Named representatives for order `81` (p = 3) -/

noncomputable abbrev order81_A1 : Type := orderP4Abel_A1 3
noncomputable abbrev order81_A2 : Type := orderP4Abel_A2 3
noncomputable abbrev order81_A3 : Type := orderP4Abel_A3 3
noncomputable abbrev order81_A4 : Type := orderP4Abel_A4 3
noncomputable abbrev order81_A5 : Type := orderP4Abel_A5 3

/-! ### Cardinalities -/

/-- Each representative has cardinality `p^4`. -/
theorem card_orderP4Abel_reps (p : ℕ) [Fact p.Prime] (i : Fin 5) :
    Nat.card (orderP4Abel_reps p i) = p ^ 4 := by
  rw [orderP4Abel_reps, card_partitionGroup p (idxToPartition i)]

theorem card_orderP4Abel_A1 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A1 p) = p ^ 4 :=
  card_orderP4Abel_reps p 0

theorem card_orderP4Abel_A2 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A2 p) = p ^ 4 :=
  card_orderP4Abel_reps p 1

theorem card_orderP4Abel_A3 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A3 p) = p ^ 4 :=
  card_orderP4Abel_reps p 2

theorem card_orderP4Abel_A4 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A4 p) = p ^ 4 :=
  card_orderP4Abel_reps p 3

theorem card_orderP4Abel_A5 (p : ℕ) [Fact p.Prime] : Nat.card (orderP4Abel_A5 p) = p ^ 4 :=
  card_orderP4Abel_reps p 4

/-! ### Specialised cardinalities: order `16` -/

theorem card_order16_A1 : Nat.card order16_A1 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A1, card_orderP4Abel_A1 2]; norm_num

theorem card_order16_A2 : Nat.card order16_A2 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A2, card_orderP4Abel_A2 2]; norm_num

theorem card_order16_A3 : Nat.card order16_A3 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A3, card_orderP4Abel_A3 2]; norm_num

theorem card_order16_A4 : Nat.card order16_A4 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A4, card_orderP4Abel_A4 2]; norm_num

theorem card_order16_A5 : Nat.card order16_A5 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [order16_A5, card_orderP4Abel_A5 2]; norm_num

/-! ### Specialised cardinalities: order `81` -/

theorem card_order81_A1 : Nat.card order81_A1 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A1, card_orderP4Abel_A1 3]; norm_num

theorem card_order81_A2 : Nat.card order81_A2 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A2, card_orderP4Abel_A2 3]; norm_num

theorem card_order81_A3 : Nat.card order81_A3 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A3, card_orderP4Abel_A3 3]; norm_num

theorem card_order81_A4 : Nat.card order81_A4 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A4, card_orderP4Abel_A4 3]; norm_num

theorem card_order81_A5 : Nat.card order81_A5 = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [order81_A5, card_orderP4Abel_A5 3]; norm_num

/-! ### Classification of partitions of `4` -/

private lemma card_le_sum_of_pos {s : Multiset ℕ} (h : ∀ i ∈ s, 0 < i) : s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 0 < a := h a (Multiset.mem_cons_self a s)
    have ha1 : 1 ≤ a := by omega
    have hs : ∀ i ∈ s, 0 < i := by
      intro i hi; exact h i (Multiset.mem_cons_of_mem hi)
    have hcards : s.card ≤ s.sum := ih hs
    rw [Multiset.card_cons, Multiset.sum_cons]
    simpa [add_comm] using add_le_add hcards ha1

/-- Every integer partition of `4` is one of the five standard ones. -/
lemma partitions_of_four (lam : Nat.Partition 4) :
    lam = part4 ∨ lam = part31 ∨ lam = part22 ∨ lam = part211 ∨ lam = part1111 := by
  have hsum : lam.parts.sum = 4 := lam.parts_sum
  have hpos : ∀ i ∈ lam.parts, 1 ≤ i := by
    intro i hi; have h := lam.parts_pos hi; omega
  have hpos' : ∀ i ∈ lam.parts, 0 < i := fun i hi => lam.parts_pos hi
  have hcard_pos : 0 < lam.parts.card := by
    by_contra! h
    have h0 : lam.parts.card = 0 := by omega
    have hempty : lam.parts = 0 := Multiset.card_eq_zero.mp h0
    rw [hempty, Multiset.sum_zero] at hsum
    omega
  have hcard_le_4 : lam.parts.card ≤ 4 := by
    have := card_le_sum_of_pos hpos'
    rw [hsum] at this
    exact this
  have hcard_cases : lam.parts.card = 1 ∨ lam.parts.card = 2 ∨
    lam.parts.card = 3 ∨ lam.parts.card = 4 := by
    omega
  rcases hcard_cases with (h1|h2|h3|h4)
  · -- Card = 1 → {4}
    rcases Multiset.card_eq_one.mp h1 with ⟨a, ha⟩
    have ha4 : a = 4 := by
      rw [ha, Multiset.sum_singleton] at hsum
      exact hsum
    have hp_eq : lam.parts = {4} := by rw [ha, ha4]
    left
    refine Nat.Partition.ext ?_
    simpa [part4] using hp_eq
  · -- Card = 2 → {3,1} or {2,2}
    have hmem : ∃ a, a ∈ lam.parts :=
      (Multiset.card_pos_iff_exists_mem.mp hcard_pos)
    rcases hmem with ⟨a, ha⟩
    rcases Multiset.exists_cons_of_mem ha with ⟨s, hs⟩
    rw [hs, Multiset.card_cons] at h2
    have hs_card1 : s.card = 1 := by omega
    rcases Multiset.card_eq_one.mp hs_card1 with ⟨b, hb⟩
    have hp_eq : lam.parts = a ::ₘ {b} := by
      rw [hs, hb]
    have hab_sum : a + b = 4 := by
      have : ((a ::ₘ {b} : Multiset ℕ)).sum = 4 := by rw [← hp_eq, hsum]
      simpa [Multiset.sum_cons, Multiset.sum_singleton] using this
    have ha1 : 1 ≤ a := hpos a (by rw [hp_eq]; simp)
    have hb1 : 1 ≤ b := hpos b (by rw [hp_eq]; simp)
    by_cases h3 : a = 3 ∨ b = 3
    · rcases h3 with (ha3 | hb3)
      · have hb1' : b = 1 := by omega
        have hp_eq' : lam.parts = 3 ::ₘ {1} := by
          rw [hp_eq, ha3, hb1']
        right; left
        refine Nat.Partition.ext ?_
        simpa [part31] using hp_eq'
      · have ha1' : a = 1 := by omega
        have hp_eq' : lam.parts = 3 ::ₘ {1} := by
          rw [hp_eq, ha1', hb3]; decide
        right; left
        refine Nat.Partition.ext ?_
        simpa [part31] using hp_eq'
    · have ha2 : a = 2 := by
        have : a = 1 ∨ a = 2 ∨ a = 4 := by omega
        rcases this with (rfl|rfl|rfl)
        · have : b = 3 := by omega
          exact (h3 (Or.inr this)).elim
        · rfl
        · omega
      have hb2 : b = 2 := by omega
      have hp_eq' : lam.parts = 2 ::ₘ {2} := by
        rw [hp_eq, ha2, hb2]
      right; right; left
      refine Nat.Partition.ext ?_
      simpa [part22] using hp_eq'
  · -- Card = 3 → {2,1,1}
    have hmem : ∃ a, a ∈ lam.parts :=
      (Multiset.card_pos_iff_exists_mem.mp hcard_pos)
    rcases hmem with ⟨a, ha⟩
    rcases Multiset.exists_cons_of_mem ha with ⟨s, hs⟩
    rw [hs, Multiset.card_cons] at h3
    have hs_card2 : s.card = 2 := by omega
    have hmem2 : ∃ b, b ∈ s :=
      (Multiset.card_pos_iff_exists_mem.mp (by omega))
    rcases hmem2 with ⟨b, hb⟩
    rcases Multiset.exists_cons_of_mem hb with ⟨t, ht⟩
    rw [ht, Multiset.card_cons] at hs_card2
    have ht_card1 : t.card = 1 := by omega
    rcases Multiset.card_eq_one.mp ht_card1 with ⟨c, hc⟩
    have hp_eq : lam.parts = a ::ₘ b ::ₘ {c} := by
      rw [hs, ht, hc]
    have habc_sum : a + b + c = 4 := by
      have : ((a ::ₘ b ::ₘ {c} : Multiset ℕ)).sum = 4 := by rw [← hp_eq, hsum]
      have : a + (b + c) = 4 := by
        simpa [Multiset.sum_cons, Multiset.sum_singleton] using this
      omega
    have ha1 : 1 ≤ a := hpos a (by rw [hp_eq]; simp)
    have hb1 : 1 ≤ b := hpos b (by rw [hp_eq]; simp)
    have hc1 : 1 ≤ c := hpos c (by rw [hp_eq]; simp)
    have hcases : (a = 2 ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = 2 ∧ c = 1) ∨
        (a = 1 ∧ b = 1 ∧ c = 2) := by
      omega
    rcases hcases with (⟨ha2, hb1', hc1'⟩|⟨ha1', hb2, hc1'⟩|⟨ha1', hb1', hc2⟩)
    · have hp_eq' : lam.parts = 2 ::ₘ 1 ::ₘ {1} := by
        rw [hp_eq, ha2, hb1', hc1']
      right; right; right; left
      refine Nat.Partition.ext ?_
      simpa [part211] using hp_eq'
    · have hp_eq' : lam.parts = 2 ::ₘ 1 ::ₘ {1} := by
        rw [hp_eq, ha1', hb2, hc1']; decide
      right; right; right; left
      refine Nat.Partition.ext ?_
      simpa [part211] using hp_eq'
    · have hp_eq' : lam.parts = 2 ::ₘ 1 ::ₘ {1} := by
        rw [hp_eq, ha1', hb1', hc2]; decide
      right; right; right; left
      refine Nat.Partition.ext ?_
      simpa [part211] using hp_eq'
  · -- Card = 4 → {1,1,1,1}
    have hmem : ∃ a, a ∈ lam.parts :=
      (Multiset.card_pos_iff_exists_mem.mp hcard_pos)
    rcases hmem with ⟨a, ha⟩
    rcases Multiset.exists_cons_of_mem ha with ⟨s, hs⟩
    rw [hs, Multiset.card_cons] at h4
    have hs_card3 : s.card = 3 := by omega
    have hmem2 : ∃ b, b ∈ s :=
      (Multiset.card_pos_iff_exists_mem.mp (by omega))
    rcases hmem2 with ⟨b, hb⟩
    rcases Multiset.exists_cons_of_mem hb with ⟨t, ht⟩
    rw [ht, Multiset.card_cons] at hs_card3
    have ht_card2 : t.card = 2 := by omega
    have hmem3 : ∃ c, c ∈ t :=
      (Multiset.card_pos_iff_exists_mem.mp (by omega))
    rcases hmem3 with ⟨c, hc⟩
    rcases Multiset.exists_cons_of_mem hc with ⟨u, hu⟩
    rw [hu, Multiset.card_cons] at ht_card2
    have hu_card1 : u.card = 1 := by omega
    rcases Multiset.card_eq_one.mp hu_card1 with ⟨d, hd⟩
    have hp_eq : lam.parts = a ::ₘ b ::ₘ c ::ₘ {d} := by
      rw [hs, ht, hu, hd]
    have habcd_sum : a + b + c + d = 4 := by
      have : ((a ::ₘ b ::ₘ c ::ₘ {d} : Multiset ℕ)).sum = 4 := by rw [← hp_eq, hsum]
      have : a + (b + (c + d)) = 4 := by
        simpa [Multiset.sum_cons, Multiset.sum_singleton] using this
      omega
    have ha1 : 1 ≤ a := hpos a (by rw [hp_eq]; simp)
    have hb1 : 1 ≤ b := hpos b (by rw [hp_eq]; simp)
    have hc1 : 1 ≤ c := hpos c (by rw [hp_eq]; simp)
    have hd1 : 1 ≤ d := hpos d (by rw [hp_eq]; simp)
    have ha1' : a = 1 := by omega
    have hb1' : b = 1 := by omega
    have hc1' : c = 1 := by omega
    have hd1' : d = 1 := by omega
    have hp_eq' : lam.parts = 1 ::ₘ 1 ::ₘ 1 ::ₘ {1} := by
      rw [hp_eq, ha1', hb1', hc1', hd1']
    right; right; right; right
    refine Nat.Partition.ext ?_
    simpa [part1111] using hp_eq'

/-! ### Completeness, distinctness, and the main classification -/

/-- Every abelian group of order `p^4` is isomorphic to one of the five standard representatives. -/
theorem orderP4Abel_complete (p : ℕ) [Fact p.Prime] (G : Type*) [CommGroup G]
    (hcard : Nat.card G = p ^ 4) : ∃ i, Nonempty (G ≃* orderP4Abel_reps p i) := by
  obtain ⟨lam, ⟨e⟩⟩ := abelian_pa_classification p 4 G hcard
  rcases partitions_of_four lam with rfl|rfl|rfl|rfl|rfl
  · exact ⟨0, ⟨e⟩⟩
  · exact ⟨1, ⟨e⟩⟩
  · exact ⟨2, ⟨e⟩⟩
  · exact ⟨3, ⟨e⟩⟩
  · exact ⟨4, ⟨e⟩⟩

/-- The five representatives are pairwise non-isomorphic. -/
theorem orderP4Abel_distinct (p : ℕ) [Fact p.Prime] (i j : Fin 5)
    (h : Nonempty (orderP4Abel_reps p i ≃* orderP4Abel_reps p j)) : i = j := by
  have hpart : idxToPartition i = idxToPartition j :=
    partitionGroup_distinct p h
  exact idxToPartition_injective hpart

/-- **Classification of abelian groups of order `p^4`.** There are exactly five isomorphism classes,
corresponding to the five partitions of `4`. -/
theorem orderP4Abel_classification (p : ℕ) [Fact p.Prime] :
    5 = Nat.card (Nat.Partition 4) := by
  have hcount := abelian_classCount p (orderP4Abel_reps p)
    (card_orderP4Abel_reps p) (orderP4Abel_complete p) (orderP4Abel_distinct p)
  simpa using hcount

end Smallgroups.UsefulTheorems
