/-
Copyright (c) 2026 Contributors to the Conjecture 5.5 formalization.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbelianEight
import DihedralEight
import SubgroupSylow

/-! A complete five-branch classification of groups of order eight. -/

namespace Conjecture55OrderEight

/-- Every group of order eight is cyclic, has exponent dividing two,
or is isomorphic to C₄ × C₂, D₈, or Q₈. The commutative/noncommutative
case split is proved from the group operations. -/
theorem classification_of_card_eight
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 8) :
    IsCyclic G ∨ (∀ x : G, x ^ 2 = 1) ∨
      Nonempty (G ≃* Multiplicative (ZMod 4 × ZMod 2)) ∨
      Nonempty (G ≃* DihedralGroup 4) ∨ Nonempty (G ≃* QuaternionGroup 2) := by
  classical
  by_cases hab : IsMulCommutative G
  · let : IsMulCommutative G := hab
    rcases AbelianEight.cyclic_or_exponent_two_or_mulEquiv_c4_c2 hcard with hc | he | hm
    · exact Or.inl hc
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl hm))
  · rw [isMulCommutative_iff] at hab
    push Not at hab
    exact Or.inr (Or.inr (Or.inr
      (OddOrder.Isaacs.Ch06.dihedralOrQuaternion_of_card_eight hcard hab)))

#print axioms classification_of_card_eight
end Conjecture55OrderEight
