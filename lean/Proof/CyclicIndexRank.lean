import SocleReduction

/-! Elementary abelian subgroup bounds using a cyclic subgroup of index two. -/
namespace Conjecture55CyclicIndex
universe u

/-- Every exponent-two group embedded into `G` has order at most four. -/
def SmallTwoRank (G : Type u) [Group G] : Prop :=
  ∀ (E : Type u) [Group E] [Finite E], ∀ f : E →* G,
    Function.Injective f → (∀ x : E, x ^ 2 = 1) → Nat.card E ≤ 4

/-- An exponent-two subgroup of a finite group with a cyclic subgroup of
index two has at most four elements. No classification of 2-groups is used. -/
theorem card_le_four_of_embedding_cyclic_index_two
    {P E : Type*} [Group P] [Group E] [Finite P] [Finite E]
    (A : Subgroup P) [IsCyclic A] (hindex : A.index = 2)
    (f : E →* P) (hf : Function.Injective f) (hsq : ∀ x : E, x ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  let K : Subgroup E := A.comap f
  let kf : K →* A :=
    { toFun := fun x => ⟨f x, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hkf : Function.Injective kf := by
    intro x y h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  let : IsCyclic K := isCyclic_of_injective kf hkf
  have hKpow : ∀ x : K, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    exact hsq x
  have hKd : Nat.card K ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hKpow
  have hKcard : Nat.card K ≤ 2 := Nat.le_of_dvd (by decide) hKd
  have hKi : K.index ≤ 2 := by
    rw [show K = A.comap f from rfl, A.index_comap f, ← hindex,
      ← A.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top (by simp [hindex])
  have hc := K.card_mul_index
  nlinarith

theorem smallTwoRank_of_injective
    {G H : Type u} [Group G] [Group H] (f : H →* G)
    (hf : Function.Injective f) (hG : SmallTwoRank G) : SmallTwoRank H := by
  intro E _ _ e he hsq
  exact hG E (f.comp e) (hf.comp he) hsq

/-- A Sylow group with a cyclic subgroup of index two bounds the elementary
abelian subgroups of the ambient group, regardless of its order. -/
theorem smallTwoRank_of_sylow_cyclic_index_two
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (A : Subgroup P) [IsCyclic A] (hindex : A.index = 2) :
    SmallTwoRank G := by
  intro E _ _ f hf hsq
  have hE : IsPGroup 2 E := fun x => ⟨1, by simpa using hsq x⟩
  have hrange : IsPGroup 2 f.range :=
    hE.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨Q, hQ⟩ := hrange.exists_le_sylow
  let e : E →* P := (Q.equiv P).toMonoidHom.comp
    ((Subgroup.inclusion hQ).comp f.rangeRestrict)
  have he : Function.Injective e := (Q.equiv P).injective.comp
    ((Subgroup.inclusion_injective hQ).comp (by
      intro x y h
      exact hf (congrArg Subtype.val h)))
  exact card_le_four_of_embedding_cyclic_index_two A hindex e he hsq

#print axioms card_le_four_of_embedding_cyclic_index_two
#print axioms smallTwoRank_of_injective
#print axioms smallTwoRank_of_sylow_cyclic_index_two
end Conjecture55CyclicIndex
