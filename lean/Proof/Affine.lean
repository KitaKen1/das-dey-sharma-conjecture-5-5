import Period

namespace Conjecture55FrobeniusProof
open Function
variable {U : Type*} [Group U]

def fixedSubgroup (e : U ≃* U) : Subgroup U where
  carrier := {x | e x = x}
  one_mem' := e.map_one
  mul_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb]
  inv_mem' := by intro a ha; simp only [Set.mem_setOf_eq] at *; rw [map_inv, ha]

def affinePerm (e : U ≃* U) (u : U) : Equiv.Perm U :=
  e.toEquiv.trans (Equiv.mulRight u)

@[simp] theorem affinePerm_apply (e : U ≃* U) (u x : U) :
    affinePerm e u x = e x * u := rfl

theorem affine_iterate_mul (e : U ≃* U) (u : U) (k : ℕ) (x y : U) :
    ((affinePerm e u : U → U)^[k]) (x * y) =
      (e ^ k) x * ((affinePerm e u : U → U)^[k]) y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, affinePerm_apply, map_mul,
      Function.iterate_succ_apply', affinePerm_apply, ← mul_assoc]
    congr 1
    simp [pow_succ', MulAut.mul_apply]

def fixedAffineEquiv (e : U ≃* U) (u : U) (k : ℕ) (a : U)
    (ha : IsPeriodicPt (affinePerm e u) k a) :
    fixedSubgroup (e ^ k) ≃ {x : U // IsPeriodicPt (affinePerm e u) k x} where
  toFun x := ⟨x.val * a, by
    change ((affinePerm e u : U → U)^[k]) (x.val * a) = x.val * a
    rw [affine_iterate_mul, x.prop, ha]⟩
  invFun x := ⟨x.val * a⁻¹, by
    change (e ^ k) (x.val * a⁻¹) = x.val * a⁻¹
    have h := affine_iterate_mul e u k (x.val * a⁻¹) a
    have hx : ((affinePerm e u : U → U)^[k]) x.val = x.val := x.prop
    have ha' : ((affinePerm e u : U → U)^[k]) a = a := ha
    have hcancel : (x.val * a⁻¹) * a = x.val := by group
    rw [hcancel, hx, ha'] at h
    calc
      (e ^ k) (x.val * a⁻¹) = ((e ^ k) (x.val * a⁻¹) * a) * a⁻¹ := by group
      _ = x.val * a⁻¹ := by rw [← h]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem exists_affine_periodic_card [Fintype U] (e : U ≃* U) (u : U) :
    ∃ a, IsPeriodicPt (affinePerm e u) (Fintype.card U) a := by
  classical
  apply exists_periodic_card_of_fixed_card_dvd (affinePerm e u)
  intro k ⟨a, ha⟩
  rw [← Fintype.card_congr (fixedAffineEquiv e u k a ha)]
  simpa only [Nat.card_eq_fintype_card] using
    Subgroup.card_subgroup_dvd_card (fixedSubgroup (e ^ k))

#print axioms affine_iterate_mul
#print axioms fixedAffineEquiv
#print axioms exists_affine_periodic_card
end Conjecture55FrobeniusProof
