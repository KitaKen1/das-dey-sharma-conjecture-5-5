import Order16Candidates

namespace Conjecture55Modular16
open Smallgroups.UsefulTheorems
abbrev M := order16_wild_G3
abbrev C2 := Multiplicative (ZMod 2)
abbrev A := Multiplicative (ZMod 4 × ZMod 2)

/-- Parity of the cyclic coordinate is a character of M16. -/
noncomputable def parity : M →* C2 where
  toFun x := Multiplicative.ofAdd (x.left.toAdd.val : ZMod 2)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

lemma parity_eq_one_iff (x : M) : parity x = 1 ↔ x ^ 4 = 1 := by
  have h : ∀ x : M, parity x = 1 ↔ x ^ 4 = 1 := by decide +kernel
  exact h x

lemma parity_surjective : Function.Surjective parity := by decide +kernel

/-- The parity kernel is exactly C4 × C2. -/
noncomputable def kernelEquiv : parity.ker ≃* A where
  toFun x := Multiplicative.ofAdd
    (((x.val.left.toAdd.val / 2 : ℕ) : ZMod 4), x.val.right.toAdd)
  invFun a := ⟨⟨Multiplicative.ofAdd (2 * a.toAdd.1.val : ZMod 8),
      Multiplicative.ofAdd a.toAdd.2⟩, by
    have h : ∀ a : A, parity
      ⟨Multiplicative.ofAdd (2 * a.toAdd.1.val : ZMod 8), Multiplicative.ofAdd a.toAdd.2⟩ = 1 :=
      by decide +kernel
    exact h a⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

#print axioms parity
#print axioms parity_eq_one_iff
#print axioms parity_surjective
#print axioms kernelEquiv
end Conjecture55Modular16
