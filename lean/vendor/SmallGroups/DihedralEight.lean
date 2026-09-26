import OrderEight

namespace Conjecture55OrderEight

/-- The identity and the unique involution are the only elements of Q₈
whose square is one. This finite calculation is checked by the kernel. -/
lemma quaternion_card_sq_eq_one :
    Nat.card {x : QuaternionGroup 2 // x ^ 2 = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- A finite elementary abelian subgroup of Q₈ has at most two elements. -/
lemma card_le_two_of_embedding_quaternion
    {E : Type*} [Group E] [Finite E] (e : E →* QuaternionGroup 2)
    (he : Function.Injective e) (hsq : ∀ x : E, x ^ 2 = 1) :
    Nat.card E ≤ 2 := by
  let f : E → {x : QuaternionGroup 2 // x ^ 2 = 1} := fun x =>
    ⟨e x, by rw [← map_pow, hsq x, map_one]⟩
  have hf : Function.Injective f := fun x y h => he (congrArg Subtype.val h)
  have hcard := Nat.card_le_card_of_injective f hf
  rwa [quaternion_card_sq_eq_one] at hcard

/-- A nonabelian group of order eight containing a subgroup of order four
and exponent two is the dihedral group of order eight. -/
theorem dihedral_of_card_eight_of_subgroup_exponent_two
    {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 8) (hnonab : ∃ x y : P, x * y ≠ y * x)
    (E : Subgroup P) (hEcard : Nat.card E = 4) (hEexp : Monoid.exponent E = 2) :
    Nonempty (P ≃* DihedralGroup 4) := by
  rcases OddOrder.Isaacs.Ch06.dihedralOrQuaternion_of_card_eight hcard hnonab with hD | hQ
  · exact hD
  · obtain ⟨e⟩ := hQ
    have hsq : ∀ x : E, x ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [hEexp])
    have hle := card_le_two_of_embedding_quaternion
      (e.toMonoidHom.comp E.subtype) (e.injective.comp Subtype.val_injective) hsq
    omega

#print axioms quaternion_card_sq_eq_one
#print axioms card_le_two_of_embedding_quaternion
#print axioms dihedral_of_card_eight_of_subgroup_exponent_two

end Conjecture55OrderEight
