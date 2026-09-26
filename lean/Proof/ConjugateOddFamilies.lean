import NormalizerOddExtensions

/-! Injective counting of conjugates of cyclic 2-subgroups, with odd factors. -/

namespace Conjecture55ConjugateOdd
open Conjecture55PartialCount Conjecture55CyclicExtensions Conjecture55NormalizerOdd
open Conjecture55Lean4Web.CyclicSum
noncomputable section
variable {G : Type*} [Group G] [Finite G]

abbrev Family (A : Subgroup G) := _root_.CyclicSum.ConjugateFamily A

def conjugator (A : Subgroup G) (T : Family A) : G := T.2.choose

theorem conjugator_spec (A : Subgroup G) (T : Family A) :
    T.1 = A.map (MulAut.conj (conjugator A T)).toMonoidHom := T.2.choose_spec

def conjugateExtension (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (x : Family A × CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    CyclicSubgroups G :=
  Conjecture55Lean4Web.cyclicSubgroupMap
    (MulAut.conj (conjugator A x.1)).toMonoidHom (extendOdd A hA hc x.2)

theorem conjugateExtension_contains (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (x : Family A × CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    x.1.1 ≤ (conjugateExtension A hA hc x).1 := by
  rw [conjugator_spec A x.1]
  exact Subgroup.map_mono le_sup_left

theorem conjugateExtension_card (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (x : Family A × CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    Nat.card (conjugateExtension A hA hc x).1 = 2 ^ (j + 1) * Nat.card x.2.1.1 := by
  change Nat.card ((extendOdd A hA hc x.2).1.map
    (MulAut.conj (conjugator A x.1)).toMonoidHom) = _
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, extendOdd_card]

theorem conjugateExtension_injective (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c) :
    Function.Injective (conjugateExtension A hA hc) := by
  rintro ⟨T, K⟩ ⟨U, L⟩ he
  let H := (conjugateExtension A hA hc (T, K)).1
  let : IsCyclic H := (conjugateExtension A hA hc (T, K)).2
  have hT : T.1 ≤ H := conjugateExtension_contains A hA hc (T, K)
  have hU : U.1 ≤ H := by
    change U.1 ≤ (conjugateExtension A hA hc (T, K)).1
    rw [he]
    exact conjugateExtension_contains A hA hc (U, L)
  have hTU : T = U := by
    apply Subtype.ext
    apply subgroups_eq_in_cyclic T.1 U.1 H hT hU
    rw [_root_.CyclicSum.conjugate_family_subgroup_card A T,
      _root_.CyclicSum.conjugate_family_subgroup_card A U]
  subst U
  have hKL : K = L := by
    apply extendOdd_injective A hA hc
    exact Conjecture55Lean4Web.cyclicSubgroupMap_injective
      (MulAut.conj (conjugator A T)).toMonoidHom (MulAut.conj _).injective he
  exact Prod.ext rfl hKL

abbrev CyclicWithTwoPart (G : Type*) [Group G] (j : ℕ) :=
  {H : CyclicSubgroups G // ∃ d : ℕ, Odd d ∧ Nat.card H.1 = 2 ^ (j + 1) * d}

def conjugateExtensionWithTwoPart (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (x : Family A × CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    CyclicWithTwoPart G j :=
  ⟨conjugateExtension A hA hc x,
    ⟨Nat.card x.2.1.1, Odd.of_dvd_nat hc x.2.2, conjugateExtension_card A hA hc x⟩⟩

theorem normalizer_index_mul_partialCount_le (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c) :
    (Subgroup.normalizer (A : Set G)).index *
      Nat.card (CyclicDividing (Subgroup.normalizer (A : Set G)) c) ≤
        Nat.card (CyclicWithTwoPart G j) := by
  have hi : Function.Injective (conjugateExtensionWithTwoPart A hA hc) := by
    intro x y he
    exact conjugateExtension_injective A hA hc (congrArg Subtype.val he)
  have h := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_prod, _root_.CyclicSum.conjugate_family_card A] at h
  exact h

/-- The normalizer's odd-divisor count can be repeated independently over
all conjugates of the cyclic 2-subgroup. -/
theorem normalizer_index_mul_divisors_le (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (hcdiv : c ∣ Nat.card (Subgroup.normalizer (A : Set G))) :
    (Subgroup.normalizer (A : Set G)).index * c.divisors.card ≤
      Nat.card (CyclicWithTwoPart G j) := by
  classical
  let := Fintype.ofFinite (Subgroup.normalizer (A : Set G))
  exact (Nat.mul_le_mul_left _ (divisors_card_le_cyclicDividing hcdiv)).trans
    (normalizer_index_mul_partialCount_le A hA hc)

#print axioms conjugateExtension_injective
#print axioms normalizer_index_mul_partialCount_le
#print axioms normalizer_index_mul_divisors_le
end
end Conjecture55ConjugateOdd
