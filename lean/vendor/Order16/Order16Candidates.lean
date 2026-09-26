import Order16Library.UsefulTheorems.Order16_Wild

/-! Refine the verified order-16 classification to the cases required by the
cyclic-index-two reduction. The quaternion case is excluded only when an
actual subgroup of order four and exponent two is supplied. -/
namespace Conjecture55OrderSixteen
open Smallgroups.UsefulTheorems

/-- Identify the classified D16 model with Mathlib's dihedral group.
The finite multiplication and inverse tables are checked in the kernel. -/
noncomputable def dihedral16Equiv : order16_wild_G4 ≃* DihedralGroup 8 where
  toFun g := if g.right.toAdd = 0 then DihedralGroup.r g.left.toAdd
    else DihedralGroup.sr (-g.left.toAdd)
  invFun
    | DihedralGroup.r i => ⟨Multiplicative.ofAdd i, Multiplicative.ofAdd 0⟩
    | DihedralGroup.sr i => ⟨Multiplicative.ofAdd (-i), Multiplicative.ofAdd 1⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

/-- An element of order eight makes the fourth-root set a proper subset. -/
lemma fourth_root_card_ne_card {P : Type*} [Group P] [Finite P]
    (x : P) (hx : orderOf x = 8) :
    pow_eq_one_card P 4 ≠ Nat.card P := by
  intro h
  have hsurj := ((Nat.bijective_iff_injective_and_card
    (Subtype.val : {g : P // g ^ 4 = 1} → P)).mpr
      ⟨Subtype.val_injective, h⟩).2
  obtain ⟨y, hy⟩ := hsurj x
  have hp : x ^ 4 = 1 := hy ▸ y.property
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hx] at hd
  norm_num at hd

/-- Without assuming noncommutativity, the only noncyclic order-16 groups
with an element of order eight are C8 × C2, SD16, M16, D16 and Q16. -/
theorem classification_of_order8 {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 16) (hnc : ¬ IsCyclic P)
    (x : P) (hx : orderOf x = 8) :
    ∃ i : Fin 14, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) ∧
      Nonempty (P ≃* order16_wild_reps i) := by
  obtain ⟨i, ⟨e⟩⟩ := order16_wild_classification hcard
  have hne : order16_wild_pow_four_card i ≠ 16 := by
    rw [← pow_four_card_order16_wild_reps,
      ← pow_eq_one_card_eq_of_mulEquiv 4 e, ← hcard]
    exact fourth_root_card_ne_card x hx
  have hi6 : i ≠ 6 := by
    intro hi
    subst i
    obtain ⟨ec⟩ := order16_A1_iso_concrete
    have e' : P ≃* Multiplicative (ZMod 16) := e.trans ec
    exact hnc (isCyclic_of_injective e'.toMonoidHom e'.injective)
  refine ⟨i, ?_, ⟨e⟩⟩
  fin_cases i
  all_goals first | exact (hne rfl).elim | exact (hi6 rfl).elim | decide

/-- The two square roots of one in Q16 are checked in the Lean kernel. -/
lemma quaternion16_card_sq_eq_one :
    Nat.card {x : QuaternionGroup 4 // x ^ 2 = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma card_le_two_of_embedding_quaternion16
    {E : Type*} [Group E] [Finite E] (e : E →* QuaternionGroup 4)
    (he : Function.Injective e) (hsq : ∀ x : E, x ^ 2 = 1) :
    Nat.card E ≤ 2 := by
  let f : E → {x : QuaternionGroup 4 // x ^ 2 = 1} := fun x =>
    ⟨e x, by rw [← map_pow, hsq x, map_one]⟩
  have hf : Function.Injective f := fun x y h => he (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  rwa [quaternion16_card_sq_eq_one] at hc

/-- A Klein-four embedding removes Q16, leaving precisely four candidates.
No claim that the remaining candidates are excluded is made here. -/
theorem classification_of_order8_of_klein_embedding
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    (hcard : Nat.card P = 16) (hnc : ¬ IsCyclic P)
    (x : P) (hx : orderOf x = 8)
    (f : E →* P) (hf : Function.Injective f)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    ∃ i : Fin 14, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) ∧
      Nonempty (P ≃* order16_wild_reps i) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := classification_of_order8 hcard hnc x hx
  have hne : i ≠ 5 := by
    intro h
    subst i
    have he : P ≃* QuaternionGroup 4 := e
    have hle := card_le_two_of_embedding_quaternion16
      (he.toMonoidHom.comp f) (he.injective.comp hf) hsq
    omega
  refine ⟨i, ?_, ⟨e⟩⟩
  rcases hi with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (hne h).elim

#print axioms Smallgroups.UsefulTheorems.order16_wild_classification
#print axioms dihedral16Equiv
#print axioms Smallgroups.UsefulTheorems.order16_wild_isClassif
#print axioms Smallgroups.UsefulTheorems.classify_of_order8_refined
#print axioms fourth_root_card_ne_card
#print axioms classification_of_order8
#print axioms quaternion16_card_sq_eq_one
#print axioms card_le_two_of_embedding_quaternion16
#print axioms classification_of_order8_of_klein_embedding
end Conjecture55OrderSixteen
