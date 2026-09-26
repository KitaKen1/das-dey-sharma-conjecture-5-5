/-
Copyright (c) 2026 Contributors to the Conjecture 5.5 formalization.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SocleReduction

/-! Lifting a simple-group Klein-four input to a finite radical-free group. -/
namespace Conjecture55RadicalV4
open Subgroup OddOrder.Isaacs
open scoped IsMulCommutative
universe u

/-- A nontrivial finite radical-free group contains a nonabelian simple subgroup;
no restriction on its order or Sylow subgroups is assumed. -/
theorem exists_injective_nonabelian_simple
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    ∃ (S : Type u) (_ : Group S) (_ : Finite S),
      IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
        ∃ i : S →* G, Function.Injective i := by
  classical
  obtain ⟨N, hN, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  have hnc : ¬IsMulCommutative N := by
    intro hcomm
    let : IsMulCommutative N := hcomm
    exact hN.2.1 (hrad N hN.1 inferInstance)
  have hss := (Ch09.isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hN).resolve_left hnc
  let : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN.2.1
  obtain ⟨X, hX, hsup⟩ := hss
  have hne : X.Nonempty := by
    by_contra h
    have he : X = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, sSup_empty] at hsup
    exact bot_ne_top hsup
  obtain ⟨S, hS⟩ := hne
  exact ⟨S, inferInstance, inferInstance, (hX S hS).2.1, (hX S hS).2.2,
    N.subtype.comp S.subtype, N.subtype_injective.comp S.subtype_injective⟩

/-- The simple-group V₄ theorem suffices for every nontrivial radical-free group.
This reduction does not assume the invalid extension to all nonsolvable groups. -/
theorem exists_card_four_exponent_two_of_radicalFree
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hV4 : ∀ (S : Type u) [Group S] [Finite S],
      IsSimpleGroup S → ¬IsMulCommutative S →
      ∃ E : Subgroup S, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1) :
    ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1 := by
  obtain ⟨S, hgroup, hfinite, hsimple, hnonab, i, hi⟩ :=
    exists_injective_nonabelian_simple hrad
  let : Group S := hgroup
  let : Finite S := hfinite
  obtain ⟨E, hcard, hpow⟩ := hV4 S hsimple hnonab
  let e := E.equivMapOfInjective i hi
  refine ⟨E.map i, (Nat.card_congr e.toEquiv).symm.trans hcard, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← map_pow, hpow y, map_one]

#print axioms exists_injective_nonabelian_simple
#print axioms exists_card_four_exponent_two_of_radicalFree
end Conjecture55RadicalV4
