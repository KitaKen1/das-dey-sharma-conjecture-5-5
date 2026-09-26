/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.CenterInvariant
import Order16Library.UsefulTheorems.P3Group.Structural
import Order16Library.UsefulTheorems.PrimeOrderClassification
import Order16Library.UsefulTheorems.PrimeSqClassification
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow

/-!
# Center cardinality of non-abelian groups of order `p^4`

For a non-abelian group of order `p^4` (`p` prime), the center has order exactly `p` or `p^2`.
The possibilities `p^3` and `p^4` are ruled out:

* `|Z(G)| = p^4` would mean `Z(G) = G`, i.e. `G` is abelian.
* `|Z(G)| = p^3` would give `|G/Z(G)| = p`, a cyclic quotient, which forces `G` to be abelian
  by `comm_of_cyclic_center_quotient`.

This is the key structural input for the non-abelian classification of order `p^4`.

## Main results

* `center_card_eq_p_or_p_sq_of_nonabelian_p4` — the center has order `p` or `p^2`
* `center_classification_of_nonabelian_p4` — the center is isomorphic to `CyclicRep p`,
  `CyclicRep (p^2)`, or `ElemAbelianRep p` (`ℤ/p × ℤ/p`)
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

variable {p : ℕ} [Fact p.Prime]

/-- Every group of order `p^4` has a normal subgroup of order `p^3`. -/
theorem exists_normal_subgroup_card_p_cube_of_card_p4 {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = p ^ 4) :
    ∃ H : Subgroup G, H.Normal ∧ Nat.card H = p ^ 3 := by
  have hp : p.Prime := Fact.out
  have hG : IsPGroup p G := IsPGroup.of_card (p := p) (n := 4) hcard
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (G := G) (p := p) (n := 3) hp hG (by
      rw [hcard]
      exact Nat.pow_le_pow_right hp.pos (by norm_num : 3 ≤ 4))
  have hindex : H.index = p := by
    have hmul := H.card_mul_index
    rw [hHcard, hcard] at hmul
    have hmul' : p ^ 3 * H.index = p ^ 3 * p := by
      calc
        p ^ 3 * H.index = p ^ 4 := hmul
        _ = p ^ 3 * p := by ring
    exact mul_left_cancel₀ (pow_ne_zero 3 hp.ne_zero) hmul'
  have hnormal : H.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hindex, hcard]
    exact (hp.pow_minFac (by norm_num : 4 ≠ 0)).symm
  exact ⟨H, hnormal, hHcard⟩

/-- If a subgroup of order `p^3` contains a central subgroup of order `p^2`, then it is
abelian.  Equivalently, quotienting by that central subgroup gives a cyclic group of prime
order, so the kernel of the quotient map is central. -/
theorem isMulCommutative_of_center_subgroup_card_p_sq_card_p_cube {G : Type*} [Group G]
    {H K : Subgroup G} (hHK : H ≤ K)
    (hHcentral : H.subgroupOf K ≤ Subgroup.center K)
    (hHcard : Nat.card H = p ^ 2) (hKcard : Nat.card K = p ^ 3) :
    IsMulCommutative K := by
  let Hsub : Subgroup K := H.subgroupOf K
  have hHsub_center : Hsub ≤ Subgroup.center K := hHcentral
  haveI : Hsub.Normal := by
    refine ⟨?_⟩
    intro n hn g
    have hncenter : n ∈ Subgroup.center K := hHsub_center hn
    have hcomm := Subgroup.mem_center_iff.mp hncenter g
    simpa [Hsub, hcomm] using hn
  have hHsub_card : Nat.card Hsub = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hHcard]
  have hquot_card : Nat.card (K ⧸ Hsub) = p := by
    have hp : p.Prime := Fact.out
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup Hsub
    rw [hKcard, hHsub_card] at hmul
    have hmul' : Nat.card (K ⧸ Hsub) * p ^ 2 = p * p ^ 2 := by
      rw [← hmul]
      ring
    exact mul_right_cancel₀ (pow_ne_zero 2 hp.ne_zero) hmul'
  haveI : IsCyclic (K ⧸ Hsub) := isCyclic_of_prime_card hquot_card
  let q : K →* K ⧸ Hsub := QuotientGroup.mk' Hsub
  have hker_le : q.ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
    exact hHsub_center
  exact q.isMulCommutative_of_isCyclic_of_ker_le_center hker_le

/-- If a subgroup of order `p^3` contains the center of `G`, and the center has order `p^2`,
then the subgroup is abelian. -/
theorem isMulCommutative_of_center_le_subgroup_card_p_cube {G : Type*} [Group G]
    {K : Subgroup G} (hcenter_le : Subgroup.center G ≤ K)
    (hcenter_card : Nat.card (Subgroup.center G) = p ^ 2)
    (hKcard : Nat.card K = p ^ 3) :
    IsMulCommutative K := by
  refine isMulCommutative_of_center_subgroup_card_p_sq_card_p_cube
    (p := p) (G := G) (H := Subgroup.center G) (K := K) hcenter_le ?_
    hcenter_card hKcard
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro k
  ext
  exact Subgroup.mem_center_iff.mp hz k.1

/-- If `|G| = p^4` and `|Z(G)| = p^2`, then `G` has an abelian subgroup of order `p^3`. -/
theorem exists_abelian_subgroup_card_p_cube_of_center_card_p_sq {G : Type*} [Group G]
    [Finite G] (hcard : Nat.card G = p ^ 4)
    (hcenter_card : Nat.card (Subgroup.center G) = p ^ 2) :
    ∃ K : Subgroup G, Nat.card K = p ^ 3 ∧ IsMulCommutative K := by
  have hp : p.Prime := Fact.out
  have hquot_card : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    rw [hcard, hcenter_card] at hmul
    have hmul' : Nat.card (G ⧸ Subgroup.center G) * p ^ 2 = p ^ 2 * p ^ 2 := by
      rw [← hmul]
      ring
    exact mul_right_cancel₀ (pow_ne_zero 2 hp.ne_zero) hmul'
  have hquot_pgroup : IsPGroup p (G ⧸ Subgroup.center G) :=
    IsPGroup.of_card (p := p) (n := 2) hquot_card
  obtain ⟨Q, hQcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (G := G ⧸ Subgroup.center G) (p := p) (n := 1) hp hquot_pgroup (by
      rw [hquot_card]
      exact Nat.pow_le_pow_right hp.pos (by norm_num : 1 ≤ 2))
  let K : Subgroup G := Q.comap (QuotientGroup.mk' (Subgroup.center G))
  have hcenter_le_K : Subgroup.center G ≤ K :=
    QuotientGroup.le_comap_mk' (Subgroup.center G) Q
  have hKcard : Nat.card K = p ^ 3 := by
    have hpre := QuotientGroup.card_preimage_mk
      (Subgroup.center G) (Q : Set (G ⧸ Subgroup.center G))
    change Nat.card (QuotientGroup.mk ⁻¹' (Q : Set (G ⧸ Subgroup.center G))) = p ^ 3
    rw [hpre, hcenter_card]
    change p ^ 2 * Nat.card Q = p ^ 3
    rw [hQcard]
    ring
  refine ⟨K, hKcard, ?_⟩
  exact isMulCommutative_of_center_le_subgroup_card_p_cube
    (p := p) (G := G) hcenter_le_K hcenter_card hKcard

/-- If `|Z(G)| = p` and a noncentral element has centralizer of order `p^3`, then that
centralizer is abelian. -/
theorem isMulCommutative_centralizer_singleton_of_card_p_cube_of_center_card_p
    {G : Type*} [Group G] [Finite G] {x : G}
    (hx_not_center : x ∉ Subgroup.center G)
    (hcenter_card : Nat.card (Subgroup.center G) = p)
    (hCcard : Nat.card (Subgroup.centralizer ({x} : Set G)) = p ^ 3) :
    IsMulCommutative (Subgroup.centralizer ({x} : Set G)) := by
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  classical
  haveI : Fintype C := Fintype.ofFinite C
  by_contra hcomm
  rw [isMulCommutative_iff] at hcomm
  have hcenterC_card : Nat.card (Subgroup.center C) = p := by
    exact P3Group.center_card_eq_p_of_nonabelian (p := p) (G := C)
      (show Nat.card C = p ^ 3 from by simpa [C] using hCcard) hcomm
  have hZ_le_C : Subgroup.center G ≤ C := by
    intro z hz
    change z ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hz x).symm
  have hZsub_centerC : (Subgroup.center G).subgroupOf C ≤ Subgroup.center C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro c
    ext
    exact Subgroup.mem_center_iff.mp hz c.1
  have hZsub_card : Nat.card ((Subgroup.center G).subgroupOf C) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ_le_C).toEquiv, hcenter_card]
  have hZsub_eq_centerC : (Subgroup.center G).subgroupOf C = Subgroup.center C := by
    exact Subgroup.eq_of_le_of_card_ge hZsub_centerC (by rw [hcenterC_card, hZsub_card])
  have hxC : x ∈ C := by
    change x ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hx_centerC : (⟨x, hxC⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hxZsub : (⟨x, hxC⟩ : C) ∈ (Subgroup.center G).subgroupOf C := by
    rw [hZsub_eq_centerC]
    exact hx_centerC
  exact hx_not_center hxZsub

/-- In a non-abelian group of order `p^4`, the center has order `p` or `p^2`. -/
theorem center_card_eq_p_or_p_sq_of_nonabelian_p4 {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = p ^ 4) (hnonab : ¬ (∀ a b : G, a * b = b * a)) :
    Nat.card (center G) = p ∨ Nat.card (center G) = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hG : IsPGroup p G := IsPGroup.of_card hcard
  have hGc : IsPGroup p (center G) := hG.to_subgroup _
  obtain ⟨k, hk_center⟩ := (IsPGroup.iff_card.mp hGc)
  -- hk_center : Nat.card (center G) = p ^ k
  have hk_le_4 : k ≤ 4 := by
    have hdv : Nat.card (center G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rw [hk_center, hcard] at hdv
    rwa [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hdv
  have hk_ge_1 : 1 ≤ k := by
    haveI : Nontrivial (center G) :=
      center_nontrivial_of_card_prime_pow hcard (by norm_num : 0 < 4)
    have h_one_lt : 1 < Nat.card (center G) :=
      Finite.one_lt_card_iff_nontrivial.mpr (by infer_instance)
    rw [hk_center] at h_one_lt
    by_contra! h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at h_one_lt
    omega
  have hk_ne_4 : k ≠ 4 := by
    intro hk4
    subst hk4
    have htop : center G = ⊤ :=
      eq_top_of_card_eq _ (hk_center.trans hcard.symm)
    exact hnonab (center_eq_top_iff.mp htop)
  have hk_ne_3 : k ≠ 3 := by
    intro hk3
    subst hk3
    have hlag := card_mul_index (center G)
    rw [index_eq_card, hk_center, hcard] at hlag
    have hquot_card : Nat.card (G ⧸ center G) = p := by
      have : p ^ 3 * Nat.card (G ⧸ center G) = p ^ 3 * p := by
        rw [hlag]; ring
      exact mul_left_cancel₀ (pow_ne_zero 3 hp.ne_zero) this
    haveI : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hquot_card
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => comm_of_cyclic_center_quotient a b
    exact hnonab hcomm
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
  · exact Or.inl (by simpa using hk_center)
  · exact Or.inr (by simpa using hk_center)

/-- In a non-abelian group of order `p^4`, the center, as a group up to isomorphism, is either
the cyclic group `ℤ/p`, the cyclic group `ℤ/p²`, or the elementary abelian group `ℤ/p × ℤ/p`. -/
theorem center_classification_of_nonabelian_p4 {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = p ^ 4) (hnonab : ¬ (∀ a b : G, a * b = b * a)) :
    Nonempty (center G ≃* CyclicRep p) ∨
    Nonempty (center G ≃* CyclicRep (p ^ 2)) ∨
    Nonempty (center G ≃* ElemAbelianRep p) := by
  have hp : p.Prime := Fact.out
  rcases center_card_eq_p_or_p_sq_of_nonabelian_p4 hcard hnonab with (hc | hc)
  · left; exact prime_classification hp hc
  · rcases prime_sq_classification hc with (hcyc | helab)
    · right; left; exact hcyc
    · right; right; exact helab

end Smallgroups.UsefulTheorems
