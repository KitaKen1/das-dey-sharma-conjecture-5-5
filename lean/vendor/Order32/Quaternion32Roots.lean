import Order32Models

namespace Conjecture55OrderThirtyTwo

lemma quaternion32_card_sq_eq_one :
    Nat.card {x : QuaternionGroup 8 // x ^ 2 = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

lemma card_le_two_of_embedding_quaternion32
    {E : Type*} [Group E] [Finite E] (e : E →* QuaternionGroup 8)
    (he : Function.Injective e) (hsq : ∀ x : E, x ^ 2 = 1) :
    Nat.card E ≤ 2 := by
  let f : E → {x : QuaternionGroup 8 // x ^ 2 = 1} := fun x =>
    ⟨e x, by rw [← map_pow, hsq x, map_one]⟩
  have hf : Function.Injective f := fun x y h => he (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  rwa [quaternion32_card_sq_eq_one] at hc

#print axioms quaternion32_card_sq_eq_one
#print axioms card_le_two_of_embedding_quaternion32
end Conjecture55OrderThirtyTwo
