import CyclicExtensions
import Semidihedral16Model
import Order32Models

/-! Normal cyclic subgroups of orders two, four, and eight in the remaining models. -/

namespace Conjecture55NormalCyclicChain
open Conjecture55CyclicExtensions
noncomputable section
variable {G : Type*} [Group G] [Finite G]

theorem normal_of_le_normal_cyclic (A R : Subgroup G) [IsCyclic R] [R.Normal]
    (hAR : A ≤ R) : A.Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  apply subgroups_eq_in_cyclic _ _ R
  · exact (Subgroup.map_mono hAR).trans_eq (Subgroup.Normal.map_conj_eq R g)
  · exact hAR
  · exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))

theorem exists_chain (R : Subgroup G) [IsCyclic R] [R.Normal]
    (h8 : 8 ∣ Nat.card R) :
    ∃ A : Fin 3 → Subgroup G, (∀ i, IsCyclic (A i)) ∧
      (∀ i, Nat.card (A i) = 2 ^ (i.val + 1)) ∧ (∀ i, (A i).Normal) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hex (i : Fin 3) : ∃ B : Subgroup R, Nat.card B = 2 ^ (i.val + 1) := by
    apply Sylow.exists_subgroup_card_pow_prime
    exact (pow_dvd_pow 2 (by omega : i.val + 1 ≤ 3)).trans h8
  choose B hB using hex
  let A (i : Fin 3) : Subgroup G := (B i).map R.subtype
  refine ⟨A, ?_, ?_, ?_⟩
  · intro i
    exact (Conjecture55Lean4Web.cyclicSubgroupMap R.subtype ⟨B i, inferInstance⟩).2
  · intro i
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective R)).trans (hB i)
  · intro i
    apply normal_of_le_normal_cyclic _ R
    exact Subgroup.map_subtype_le _

theorem semidirect_chain {N H : Type*} [Group N] [Group H] [Finite N] [Finite H]
    [IsCyclic N] (φ : H →* MulAut N) (h8 : 8 ∣ Nat.card N) :
    ∃ A : Fin 3 → Subgroup (SemidirectProduct N H φ), (∀ i, IsCyclic (A i)) ∧
      (∀ i, Nat.card (A i) = 2 ^ (i.val + 1)) ∧ (∀ i, (A i).Normal) := by
  let : Finite (SemidirectProduct N H φ) :=
    Finite.of_equiv (N × H) SemidirectProduct.equivProd.symm
  let f : N →* SemidirectProduct N H φ := SemidirectProduct.inl
  let R := f.range
  let : R.Normal := by
    change (SemidirectProduct.inl : N →* SemidirectProduct N H φ).range.Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  let : IsCyclic R := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  apply exists_chain R
  have hc : Nat.card R = Nat.card N := Nat.card_congr
    (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv.symm
  rwa [hc]

theorem sd16_chain :
    ∃ A : Fin 3 → Subgroup Smallgroups.UsefulTheorems.order16_wild_G2,
      (∀ i, IsCyclic (A i)) ∧ (∀ i, Nat.card (A i) = 2 ^ (i.val + 1)) ∧
      (∀ i, (A i).Normal) := by
  apply semidirect_chain
  norm_num [Nat.card_eq_fintype_card]

theorem sd32_chain :
    ∃ A : Fin 3 → Subgroup Conjecture55OrderThirtyTwo.Semidihedral32,
      (∀ i, IsCyclic (A i)) ∧ (∀ i, Nat.card (A i) = 2 ^ (i.val + 1)) ∧
      (∀ i, (A i).Normal) := by
  apply semidirect_chain
  norm_num [Nat.card_eq_fintype_card]

#print axioms normal_of_le_normal_cyclic
#print axioms exists_chain
#print axioms semidirect_chain
#print axioms sd16_chain
#print axioms sd32_chain
end
end Conjecture55NormalCyclicChain
