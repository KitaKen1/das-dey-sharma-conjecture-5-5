import CyclicIndexRank

/-! The almost-simple reduction using an elementary abelian rank bound instead
of the old restriction that sixteen does not divide the group order. -/
namespace Conjecture55RankSocle
open Subgroup OddOrder.Isaacs Conjecture55CyclicIndex
open scoped IsMulCommutative
universe u

/-- Two commuting disjoint groups containing Klein four groups cannot both
embed in a group of elementary abelian 2-rank at most two. -/
theorem false_of_disjoint_commuting_klein_four
    {G : Type u} [Group G] [Finite G] (hsmall : SmallTwoRank G)
    (S T : Subgroup G) (hd : Disjoint S T)
    (hc : ∀ (s : S) (t : T), Commute (s : G) (t : G))
    (E : Subgroup S) (hE : Nat.card E = 4) (hEsq : ∀ x : E, x ^ 2 = 1)
    (F : Subgroup T) (hF : Nat.card F = 4) (hFsq : ∀ x : F, x ^ 2 = 1) : False := by
  let f : S × T →* G := S.subtype.noncommCoprod T.subtype hc
  have hf : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    exact ⟨S.subtype_injective, T.subtype_injective, by simpa using hd⟩
  let e : E × F →* S × T := E.subtype.prodMap F.subtype
  have he : Function.Injective e := by
    intro x y h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg Prod.snd h
  have hsq : ∀ x : E × F, x ^ 2 = 1 := by
    intro x
    exact Prod.ext (hEsq x.1) (hFsq x.2)
  have hh := hsmall (E × F) (f.comp e) (hf.comp he) hsq
  norm_num [Nat.card_prod, hE, hF] at hh

theorem simple_of_semisimple_of_smallTwoRank
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hss : Ch09.IsSemisimpleGroup G) (hsmall : SmallTwoRank G)
    (hV4 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H →
      ∃ E : Subgroup H, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1) :
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
    obtain ⟨E, hE, hEsq⟩ := hV4 T (hX T hT).2.1 (hX T hT).2.2
    obtain ⟨F, hF, hFsq⟩ := hV4 S (hX S hS).2.1 (hX S hS).2.2
    apply false_of_disjoint_commuting_klein_four hsmall T S
      (Ch09.disjoint_of_isMinimalNormal_of_ne
        (Ch09.isMinimalNormal_of_mem_semisimpleFamily hX hT)
        (Ch09.isMinimalNormal_of_mem_semisimpleFamily hX hS) hTS)
      (fun t s => Ch09.commute_of_mem_semisimpleFamily_of_ne hX hT hS hTS t.2 s.2)
      E hE hEsq F hF hFsq
  have hXS : X = {S} := Set.eq_singleton_iff_unique_mem.mpr ⟨hS, hu⟩
  have hStop : S = ⊤ := by simpa [hXS] using hsup
  let e : S ≃* G := (MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv
  have : IsSimpleGroup S := (hX S hS).2.1
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  intro hcomm
  let : IsMulCommutative G := hcomm
  exact (hX S hS).2.2
    (Ch09.isMulCommutative_of_surjective e.symm.toMonoidHom e.symm.surjective)

theorem minimal_normal_isSimple_of_radicalFree_smallTwoRank
    {G : Type u} [Group G] [Finite G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsmall : SmallTwoRank G)
    (hV4 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H →
      ∃ E : Subgroup H, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1)
    {N : Subgroup G} (hN : Ch02.IsMinimalNormal N) :
    IsSimpleGroup N ∧ ¬IsMulCommutative N := by
  have hnc : ¬IsMulCommutative N := by
    intro hcomm
    let : IsMulCommutative N := hcomm
    exact hN.2.1 (hrad N hN.1 inferInstance)
  have hss := (Ch09.isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hN).resolve_left hnc
  have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN.2.1
  exact simple_of_semisimple_of_smallTwoRank hss
    (smallTwoRank_of_injective N.subtype N.subtype_injective hsmall) hV4

/-- The socle is nonabelian simple and has trivial centralizer even when
sixteen or thirty-two divides the group order. -/
theorem exists_simple_normal_centralizer_eq_bot_of_smallTwoRank
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsmall : SmallTwoRank G)
    (hV4 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H →
      ∃ E : Subgroup H, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1) :
    ∃ S : Subgroup G, S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ := by
  obtain ⟨S, hS, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  obtain ⟨hss, hsnc⟩ := minimal_normal_isSimple_of_radicalFree_smallTwoRank
    hrad hsmall hV4 hS
  refine ⟨S, hS.1, hss, hsnc, ?_⟩
  have : S.Normal := hS.1
  by_contra hC
  obtain ⟨T, hT, hTC⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (Subgroup.centralizer (S : Set G)) hC
  obtain ⟨hts, htnc⟩ := minimal_normal_isSimple_of_radicalFree_smallTwoRank
    hrad hsmall hV4 hT
  have hTS : T ≠ S := by
    intro he
    apply hsnc
    exact Subgroup.le_centralizer_iff_isMulCommutative.mp (he ▸ hTC)
  obtain ⟨E, hE, hEsq⟩ := hV4 T hts htnc
  obtain ⟨F, hF, hFsq⟩ := hV4 S hss hsnc
  exact false_of_disjoint_commuting_klein_four hsmall T S
    (Ch09.disjoint_of_isMinimalNormal_of_ne hT hS hTS)
    (fun t s => (Subgroup.mem_centralizer_iff.mp (hTC t.2) s s.2).symm)
    E hE hEsq F hF hFsq

#print axioms false_of_disjoint_commuting_klein_four
#print axioms simple_of_semisimple_of_smallTwoRank
#print axioms minimal_normal_isSimple_of_radicalFree_smallTwoRank
#print axioms exists_simple_normal_centralizer_eq_bot_of_smallTwoRank
end Conjecture55RankSocle
