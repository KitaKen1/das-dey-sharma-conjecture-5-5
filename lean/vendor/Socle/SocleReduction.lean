/-
Copyright (c) 2026 Contributors to the Conjecture 5.5 formalization.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import OddOrder.Isaacs.Ch09_MoreSubnormality.Semisimple

/-! The elementary almost-simple reduction after the external input that
nonabelian finite simple groups have order divisible by four. -/

namespace Conjecture55Socle
open Subgroup OddOrder.Isaacs
open scoped IsMulCommutative
universe u

/-- Two disjoint commuting subgroups of orders divisible by four force
sixteen to divide the ambient group order. -/
theorem sixteen_dvd_of_disjoint_commuting
    {G : Type*} [Group G] [Finite G] (S T : Subgroup G)
    (hd : Disjoint S T)
    (hc : ∀ (s : S) (t : T), Commute (s : G) (t : G))
    (hS : 4 ∣ Nat.card S) (hT : 4 ∣ Nat.card T) : 16 ∣ Nat.card G := by
  let f : S × T →* G := S.subtype.noncommCoprod T.subtype hc
  have hf : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    exact ⟨S.subtype_injective, T.subtype_injective, by simpa using hd⟩
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_prod] at hdvd
  exact (show 16 ∣ Nat.card S * Nat.card T from mul_dvd_mul hS hT).trans hdvd

/-- A nontrivial semisimple group whose order is not divisible by sixteen
has only one simple factor, provided each factor has order divisible by four. -/
theorem simple_of_semisimple_of_not_sixteen_dvd
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hss : Ch09.IsSemisimpleGroup G) (h16 : ¬16 ∣ Nat.card G)
    (hfour : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H → 4 ∣ Nat.card H) :
    IsSimpleGroup G ∧ ¬IsMulCommutative G := by
  classical
  obtain ⟨X, hX, hsup⟩ := hss
  have hne : X.Nonempty := by
    by_contra h
    have he : X = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, sSup_empty] at hsup
    exact bot_ne_top hsup
  obtain ⟨S, hS⟩ := hne
  have hu : ∀ T ∈ X, T = S := by
    intro T hT
    by_contra hTS
    apply h16
    apply sixteen_dvd_of_disjoint_commuting T S
    · exact Ch09.disjoint_of_isMinimalNormal_of_ne
        (Ch09.isMinimalNormal_of_mem_semisimpleFamily hX hT)
        (Ch09.isMinimalNormal_of_mem_semisimpleFamily hX hS) hTS
    · intro t s
      exact Ch09.commute_of_mem_semisimpleFamily_of_ne hX hT hS hTS t.2 s.2
    · exact hfour T (hX T hT).2.1 (hX T hT).2.2
    · exact hfour S (hX S hS).2.1 (hX S hS).2.2
  have hXS : X = {S} := Set.eq_singleton_iff_unique_mem.mpr ⟨hS, hu⟩
  have hStop : S = ⊤ := by simpa [hXS] using hsup
  let e : S ≃* G := (MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv
  have : IsSimpleGroup S := (hX S hS).2.1
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  intro hcomm
  let : IsMulCommutative G := hcomm
  exact (hX S hS).2.2
    (Ch09.isMulCommutative_of_surjective e.symm.toMonoidHom e.symm.surjective)

/-- Under the simple-group order input, every minimal normal subgroup of a
radical-free group with no sixteen in its order is nonabelian simple. -/
theorem minimal_normal_isSimple_of_radicalFree
    {G : Type u} [Group G] [Finite G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h16 : ¬16 ∣ Nat.card G)
    (hfour : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H → 4 ∣ Nat.card H)
    {N : Subgroup G} (hN : Ch02.IsMinimalNormal N) :
    IsSimpleGroup N ∧ ¬IsMulCommutative N := by
  have hnc : ¬IsMulCommutative N := by
    intro hcomm
    let : IsMulCommutative N := hcomm
    exact hN.2.1 (hrad N hN.1 inferInstance)
  have hss := (Ch09.isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hN).resolve_left hnc
  have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN.2.1
  exact simple_of_semisimple_of_not_sixteen_dvd hss
    (fun h => h16 (h.trans N.card_subgroup_dvd_card)) hfour

/-- A nontrivial finite radical-free group with no sixteen in its order has
a nonabelian simple normal subgroup with trivial centralizer, conditional only
on the independent simple-group order-divisibility input. -/
theorem exists_simple_normal_centralizer_eq_bot
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h16 : ¬16 ∣ Nat.card G)
    (hfour : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H → 4 ∣ Nat.card H) :
    ∃ S : Subgroup G, S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ := by
  obtain ⟨S, hS, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  obtain ⟨hss, hsnc⟩ := minimal_normal_isSimple_of_radicalFree hrad h16 hfour hS
  refine ⟨S, hS.1, hss, hsnc, ?_⟩
  have : S.Normal := hS.1
  by_contra hC
  obtain ⟨T, hT, hTC⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (Subgroup.centralizer (S : Set G)) hC
  obtain ⟨hts, htnc⟩ := minimal_normal_isSimple_of_radicalFree hrad h16 hfour hT
  have hTS : T ≠ S := by
    intro he
    apply hsnc
    exact Subgroup.le_centralizer_iff_isMulCommutative.mp (he ▸ hTC)
  apply h16
  apply sixteen_dvd_of_disjoint_commuting T S
  · exact Ch09.disjoint_of_isMinimalNormal_of_ne hT hS hTS
  · intro t s
    exact (Subgroup.mem_centralizer_iff.mp (hTC t.2) s s.2).symm
  · exact hfour T hts htnc
  · exact hfour S hss hsnc

#print axioms sixteen_dvd_of_disjoint_commuting
#print axioms simple_of_semisimple_of_not_sixteen_dvd
#print axioms minimal_normal_isSimple_of_radicalFree
#print axioms exists_simple_normal_centralizer_eq_bot
#print axioms Ch09.isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal
#print axioms Ch02.exists_isMinimalNormal_le_of_normal
end Conjecture55Socle
