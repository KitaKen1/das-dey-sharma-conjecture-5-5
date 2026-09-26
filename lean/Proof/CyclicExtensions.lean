import PartialCyclicCount
import Families

/-! Commuting coprime cyclic factors and recovery of the two factors. -/

namespace Conjecture55CyclicExtensions
noncomputable section
variable {G : Type*} [Group G] [Finite G]

theorem cyclic_subgroup_eq_of_card_eq [IsCyclic G]
    (A B : Subgroup G) (hc : Nat.card A = Nat.card B) : A = B := by
  let : CommGroup G := IsCyclic.commGroup
  have hker (A : Subgroup G) : A = (powMonoidHom (Nat.card A) : G →* G).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      change x ^ Nat.card A = 1
      exact congrArg (fun y : A => (y : G))
        (orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard (⟨x, hx⟩ : A)))
    · rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right A.card_subgroup_dvd_card]
  rw [hker A, hker B, hc]

theorem subgroups_eq_in_cyclic
    (A B H : Subgroup G) [IsCyclic H] (hA : A ≤ H) (hB : B ≤ H)
    (hc : Nat.card A = Nat.card B) : A = B := by
  have he : A.subgroupOf H = B.subgroupOf H := by
    apply cyclic_subgroup_eq_of_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hc]
  have he' := congrArg (fun K : Subgroup H => K.map H.subtype) he
  simpa only [Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB] using he'

def commutingProduct (A B : Subgroup G)
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G)) : A × B →* G :=
  A.subtype.noncommCoprod B.subtype hcomm

theorem commutingProduct_range (A B : Subgroup G)
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G)) :
    (commutingProduct A B hcomm).range = A ⊔ B := by
  change (A.subtype.noncommCoprod B.subtype hcomm).range = A ⊔ B
  erw [MonoidHom.noncommCoprod_range]
  simp

theorem commutingProduct_injective (A B : Subgroup G)
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G))
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    Function.Injective (commutingProduct A B hcomm) :=
  Subgroup.mul_injective_of_disjoint (Subgroup.disjoint_of_coprime_natCard hcop)

theorem card_sup_of_commuting_coprime (A B : Subgroup G)
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G))
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  rw [← commutingProduct_range A B hcomm,
    ← Nat.card_congr (MonoidHom.ofInjective
      (commutingProduct_injective A B hcomm hcop)).toEquiv, Nat.card_prod]

theorem cyclic_sup_of_commuting_coprime (A B : Subgroup G)
    [IsCyclic A] [IsCyclic B]
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G))
    (hcop : (Nat.card A).Coprime (Nat.card B)) : IsCyclic (A ⊔ B : Subgroup G) := by
  let : IsCyclic (A × B) := Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, hcop⟩
  rw [← commutingProduct_range A B hcomm]
  exact isCyclic_of_surjective (commutingProduct A B hcomm).rangeRestrict
    (commutingProduct A B hcomm).rangeRestrict_surjective

#print axioms cyclic_subgroup_eq_of_card_eq
#print axioms subgroups_eq_in_cyclic
#print axioms card_sup_of_commuting_coprime
#print axioms cyclic_sup_of_commuting_coprime
end
end Conjecture55CyclicExtensions
