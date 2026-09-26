import Mathlib

namespace Conjecture55FrobeniusProof

noncomputable def sigmaStabilizerEquivOrbitProd {H T : Type*} [Group H] [MulAction H T] :
    (Σ t : T, MulAction.stabilizer H t) ≃
      (Quotient (MulAction.orbitRel H T)) × H :=
  (show (Σ t : T, MulAction.stabilizer H t) ≃
      (Σ h : H, MulAction.fixedBy T h) from {
    toFun := fun ⟨t, h⟩ => ⟨h.val, ⟨t, h.prop⟩⟩
    invFun := fun ⟨h, t⟩ => ⟨t.val, ⟨h, t.prop⟩⟩
    left_inv := by rintro ⟨t, ⟨h, hh⟩⟩; rfl
    right_inv := by rintro ⟨h, ⟨t, ht⟩⟩; rfl
  }).trans (MulAction.sigmaFixedByEquivOrbitsProdGroup H T)

theorem group_card_dvd_card_of_fiber_equiv_stabilizer
    {H S T : Type*} [Group H] [Fintype H] [Fintype S] [Fintype T] [MulAction H T]
    (f : S → T) (e : ∀ t, {s : S // f s = t} ≃ MulAction.stabilizer H t) :
    Fintype.card H ∣ Fintype.card S := by
  classical
  let E := ((Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight e)).trans sigmaStabilizerEquivOrbitProd
  rw [Fintype.card_congr E, Fintype.card_prod]
  exact dvd_mul_left _ _

#print axioms group_card_dvd_card_of_fiber_equiv_stabilizer
end Conjecture55FrobeniusProof
