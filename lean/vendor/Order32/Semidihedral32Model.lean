import Order32Models

namespace Conjecture55Semidihedral32
open Multiplicative Conjecture55OrderThirtyTwo
abbrev M := Semidihedral32
abbrev B := Multiplicative (ZMod 2)

/-- Even cyclic coordinate is the dihedral subgroup of index two. -/
noncomputable def parity : M →* B where
  toFun x := ofAdd (x.left.toAdd.val : ZMod 2)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

/-- Projection onto the reflection coordinate. -/
def reflection : M →* B where
  toFun x := x.right
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def evenEquiv : parity.ker ≃* DihedralGroup 8 where
  toFun x := if x.val.right.toAdd = 0 then
      DihedralGroup.r ((x.val.left.toAdd.val / 2 : ℕ) : ZMod 8)
    else DihedralGroup.sr (-((x.val.left.toAdd.val / 2 : ℕ) : ZMod 8))
  invFun
    | DihedralGroup.r i => ⟨⟨ofAdd (2 * i.val : ZMod 16), ofAdd 0⟩, by
        have h : ∀ i : ZMod 8, parity ⟨ofAdd (2 * i.val : ZMod 16), ofAdd 0⟩ = 1 := by decide +kernel
        exact h i⟩
    | DihedralGroup.sr i => ⟨⟨ofAdd (2 * (-i).val : ZMod 16), ofAdd 1⟩, by
        have h : ∀ i : ZMod 8, parity ⟨ofAdd (2 * (-i).val : ZMod 16), ofAdd 1⟩ = 1 := by decide +kernel
        exact h i⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

lemma cyclic_involutions_card :
    Nat.card {x : M // x ^ 2 = 1 ∧ reflection x = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- An odd-coordinate element and a reflection involution generate SD32.
The finite certificate enumerates elements and exponents, never subgroups. -/
lemma generation_certificate :
    ∀ y z : M, parity y ≠ 1 → z ^ 2 = 1 → reflection z ≠ 1 →
      ∀ g : M, ∃ i : Fin 16, ∃ j : Fin 2,
        g = (if reflection y = 1 then y else y * z) ^ i.val * z ^ j.val := by
  decide +kernel

#print axioms parity
#print axioms evenEquiv
#print axioms cyclic_involutions_card
#print axioms generation_certificate
end Conjecture55Semidihedral32
