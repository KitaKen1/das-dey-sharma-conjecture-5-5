import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

open scoped BigOperators

namespace CyclicSum

noncomputable section

variable {G : Type*} [Group G] [Fintype G]

def generatorsEquiv (K : Subgroup G) :
    {x : G // Subgroup.zpowers x = K} ≃
      {x : K // orderOf x = Nat.card K} where
  toFun x := ⟨⟨x, x.2.le (Subgroup.mem_zpowers x.1)⟩, by
    rw [Subgroup.orderOf_mk, ← Nat.card_zpowers, x.2]⟩
  invFun x := ⟨x.1, by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem x.1.2)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact le_of_eq x.2.symm⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem card_generators (K : Subgroup G) [IsCyclic K] :
    Nat.card {x : G // Subgroup.zpowers x = K} = Nat.totient (Nat.card K) := by
  classical
  rw [Nat.card_congr (generatorsEquiv K), Nat.card_eq_fintype_card]
  simpa [Fintype.card_subtype, Nat.card_eq_fintype_card] using
    (IsCyclic.card_orderOf_eq_totient (α := K) (d := Fintype.card K) dvd_rfl)

#print axioms generatorsEquiv
#print axioms card_generators

abbrev CyclicSubgroups (G : Type*) [Group G] := {K : Subgroup G // IsCyclic K}

def generated (x : G) : CyclicSubgroups G := ⟨Subgroup.zpowers x, inferInstance⟩

theorem card_generated_fiber (K : CyclicSubgroups G) :
    Nat.card {x : G // generated x = K} = Nat.totient (Nat.card K.1) := by
  classical
  let : IsCyclic K.1 := K.2
  have heq : (fun x : G => generated x = K) =
      (fun x : G => Subgroup.zpowers x = K.1) := by
    funext x
    exact propext Subtype.ext_iff
  rw [heq]
  exact card_generators K.1

theorem cyclic_count_eq_sum :
    (Nat.card (CyclicSubgroups G) : ℚ) =
      ∑ x : G, (1 : ℚ) / Nat.totient (orderOf x) := by
  classical
  rw [← Fintype.sum_fiberwise (generated (G := G))]
  calc
    (Nat.card (CyclicSubgroups G) : ℚ) = ∑ _K : CyclicSubgroups G, (1 : ℚ) := by
      simp [Nat.card_eq_fintype_card]
    _ = ∑ K : CyclicSubgroups G, ∑ x : {x : G // generated x = K},
        (1 : ℚ) / Nat.totient (orderOf x.1) := by
      apply Fintype.sum_congr
      intro K
      have hx (x : {x : G // generated x = K}) : orderOf x.1 = Nat.card K.1 := by
        rw [← Nat.card_zpowers]
        exact congrArg (fun L : Subgroup G => Nat.card L) (congrArg Subtype.val x.2)
      simp_rw [hx]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, card_generated_fiber]
      have hpos : 0 < Nat.totient (Nat.card K.1) :=
        Nat.totient_pos.mpr Nat.card_pos
      field_simp

#print axioms cyclic_count_eq_sum

/-- Element-order divisibility along a bijection reverses cyclic subgroup counts. -/
theorem cyclic_count_le_of_order_dvd_equiv
    {H : Type*} [Group H] [Fintype H] (e : G ≃ H)
    (he : ∀ x : G, orderOf x ∣ orderOf (e x)) :
    Nat.card (CyclicSubgroups H) ≤ Nat.card (CyclicSubgroups G) := by
  have hsum : (Nat.card (CyclicSubgroups H) : ℚ) ≤
      (Nat.card (CyclicSubgroups G) : ℚ) := by
    rw [cyclic_count_eq_sum, cyclic_count_eq_sum, ← e.sum_comp]
    apply Finset.sum_le_sum
    intro x _
    have hposx : 0 < Nat.totient (orderOf x) := Nat.totient_pos.mpr (orderOf_pos x)
    have hpose : 0 < Nat.totient (orderOf (e x)) := Nat.totient_pos.mpr (orderOf_pos _)
    exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hposx)
      (Nat.cast_le.mpr (Nat.le_of_dvd hpose (Nat.totient_dvd_of_dvd (he x))))
  exact_mod_cast hsum

#print axioms cyclic_count_le_of_order_dvd_equiv

end

end CyclicSum
