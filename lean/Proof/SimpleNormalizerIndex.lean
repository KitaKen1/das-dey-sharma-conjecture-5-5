import Conjecture55Foundation

/-! A cyclic subgroup inside a nonabelian simple subgroup has no normalizer
of odd index one or three. No classification theorem is used. -/

namespace Conjecture55SimpleNormalizer
variable {G : Type*} [Group G] [Finite G]

theorem simple_not_le_cyclic_normalizer
    (S A : Subgroup G) (hs : IsSimpleGroup S) (hn : ¬IsMulCommutative S)
    [IsCyclic A] (hA : A ≠ ⊥) (hAS : A ≤ S) :
    ¬ S ≤ Subgroup.normalizer (A : Set G) := by
  intro hN
  have hnorm : (A.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).mpr hN
  rcases hs.eq_bot_or_eq_top_of_normal (A.subgroupOf S) hnorm with hbot | htop
  · apply hA
    have h := congrArg (fun H : Subgroup S => H.map S.subtype) hbot
    simpa only [Subgroup.map_subgroupOf_eq_of_le hAS, Subgroup.map_bot] using h
  · have h := congrArg (fun H : Subgroup S => H.map S.subtype) htop
    have he : A = S := by
      rw [Subgroup.map_subgroupOf_eq_of_le hAS, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
      exact h
    subst A
    exact hn inferInstance

theorem odd_normalizer_index_ge_five
    (S A : Subgroup G) (hs : IsSimpleGroup S) (hn : ¬IsMulCommutative S)
    (h4 : 4 ∣ Nat.card S) [IsCyclic A] (hA : A ≠ ⊥) (hAS : A ≤ S)
    (ho : Odd (Subgroup.normalizer (A : Set G)).index) :
    5 ≤ (Subgroup.normalizer (A : Set G)).index := by
  let N := Subgroup.normalizer (A : Set G)
  have hnot : ¬S ≤ N := simple_not_le_cyclic_normalizer S A hs hn hA hAS
  have h1 : N.index ≠ 1 := by
    intro he
    have ht : N = ⊤ := Subgroup.index_eq_one.mp he
    exact hnot (ht ▸ le_top)
  have h3 : N.index ≠ 3 := by
    intro he
    let C := N.normalCore
    have hfac : C.index ∣ 6 := by
      have h : N.normalCore.index ∣ N.index.factorial := by
        rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker,
          Subgroup.index_eq_card, ← Nat.card_perm]
        exact Subgroup.card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ N)).range
      norm_num [C, he] at h ⊢
      exact h
    have hbot : C.subgroupOf S = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal (C.subgroupOf S) inferInstance with hb | ht
      · exact hb
      · have hSC : S ≤ C := Subgroup.subgroupOf_eq_top.mp ht
        exact (hnot (hSC.trans N.normalCore_le)).elim
    have hrel : C.relIndex S = Nat.card S := by
      rw [Subgroup.relIndex, hbot, Subgroup.index_bot]
    have hd : Nat.card S ∣ C.index := by
      rw [← hrel]
      exact Subgroup.relIndex_dvd_index_of_normal C S
    have hbad : 4 ∣ 6 := h4.trans (hd.trans hfac)
    norm_num at hbad
  have hop : Odd N.index := ho
  have := hop.pos
  have := Nat.odd_iff.mp hop
  have hge : 5 ≤ N.index := by omega
  exact hge

#print axioms simple_not_le_cyclic_normalizer
#print axioms odd_normalizer_index_ge_five
end Conjecture55SimpleNormalizer
