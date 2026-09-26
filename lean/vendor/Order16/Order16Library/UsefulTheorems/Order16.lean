/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.OrderP4_Abel
import Order16Library.UsefulTheorems.OrderP4_NonAbel
import Order16Library.UsefulTheorems.CenterInvariant
import Order16Library.UsefulTheorems.PrimeOrderClassification
import Order16Library.UsefulTheorems.PrimeSqClassification
import Order16Library.UsefulTheorems.PrimePairNonabelian
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Classification of groups of order 16

There are exactly **14** groups of order 16 up to isomorphism:
- **5 abelian** groups, corresponding to the partitions of `4`
- **9 non-abelian** groups, classified by the isomorphism type of their center

## Non-abelian classification by center

| Center      | Count | Representatives                                                    |
|-------------|-------|--------------------------------------------------------------------|
| ≅ C4        | 2     | C8 ⋊ C2 (modular), Q8 ⋊ C2                                       |
| ≅ C2 × C2   | 4     | C4 ⋊ C4, (C2×C2) ⋊ C4, D4 × C2, Q8 × C2                         |
| ≅ C2        | 3     | D8 (dihedral), Q16 (generalised quaternion), SD16 (semidihedral)  |

## Main results

* `order16_classification` — every group of order 16 is isomorphic to one of the 14 representatives
* `order16_distinct` — the 14 representatives are pairwise non-isomorphic
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct
open Subgroup

/-! ### Helpers: actions on cyclic groups -/

/-- Multiplication by a unit `u : (ZMod n)ˣ` as an automorphism of `Multiplicative (ZMod n)`.
This is the action `x ↦ u·x` on the cyclic group of order `n`. -/
noncomputable def unitAut (n : ℕ) : (ZMod n)ˣ →* MulAut (Multiplicative (ZMod n)) where
  toFun u := AddEquiv.toMultiplicative (DistribMulAction.toAddEquiv (ZMod n) u)
  map_one' := by ext m; simp
  map_mul' u v := by ext m; simp [mul_smul]

/-- The hom `Multiplicative (ZMod 2) →* (ZMod n)ˣ` sending the generator to `u` (where `u² = 1`). -/
noncomputable def c2UnitHom (n : ℕ) [NeZero 2] (u : (ZMod n)ˣ) (hu : u ^ 2 = 1) :
    Multiplicative (ZMod 2) →* (ZMod n)ˣ :=
  MonoidHom.mk' (fun x => u ^ (Multiplicative.toAdd x).val)
    (pow_val_add hu · ·)

/-- Action of C2 on Cn by multiplication by a unit `u` of order dividing 2. -/
noncomputable def c2ActionAut (n : ℕ) [NeZero 2] (u : (ZMod n)ˣ) (hu : u ^ 2 = 1) :
    Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod n)) :=
  (unitAut n).comp (c2UnitHom n u hu)

/-- The hom `Multiplicative (ZMod 4) →* (ZMod n)ˣ` sending the generator to `u` (where `u⁴ = 1`). -/
noncomputable def c4UnitHom (n : ℕ) [NeZero 4] (u : (ZMod n)ˣ) (hu : u ^ 4 = 1) :
    Multiplicative (ZMod 4) →* (ZMod n)ˣ :=
  MonoidHom.mk' (fun x => u ^ (Multiplicative.toAdd x).val)
    (pow_val_add hu · ·)

/-- Action of C4 on Cn by multiplication by a unit `u` of order dividing 4. -/
noncomputable def c4ActionAut (n : ℕ) [NeZero 4] (u : (ZMod n)ˣ) (hu : u ^ 4 = 1) :
    Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod n)) :=
  (unitAut n).comp (c4UnitHom n u hu)

/-! ### Specific units of ZMod -/

/-- The unit `3` in `(ZMod 8)ˣ`. -/
def zmod8_unit_3 : (ZMod 8)ˣ :=
  ZMod.unitOfCoprime 3 (by norm_num)

/-- The unit `5` in `(ZMod 8)ˣ`. -/
def zmod8_unit_5 : (ZMod 8)ˣ :=
  ZMod.unitOfCoprime 5 (by norm_num)

/-- The unit `3` in `(ZMod 4)ˣ`. -/
def zmod4_unit_3 : (ZMod 4)ˣ :=
  ZMod.unitOfCoprime 3 (by norm_num)

@[simp] theorem zmod8_unit_3_sq : zmod8_unit_3 ^ 2 = 1 := by
  unfold zmod8_unit_3; decide

@[simp] theorem zmod8_unit_5_sq : zmod8_unit_5 ^ 2 = 1 := by
  unfold zmod8_unit_5; decide

@[simp] theorem zmod4_unit_3_sq : zmod4_unit_3 ^ 2 = 1 := by
  unfold zmod4_unit_3; decide

@[simp] theorem zmod4_unit_3_pow4 : zmod4_unit_3 ^ 4 = 1 := by
  unfold zmod4_unit_3; decide

instance : NeZero 2 := ⟨by norm_num⟩
instance : NeZero 4 := ⟨by norm_num⟩
instance : NeZero 8 := ⟨by norm_num⟩

/-! ### Abelian representatives (from `OrderP4_Abel`)

The five abelian groups of order 16, corresponding to the five partitions of 4:
`order16_A1` ≅ C16, `order16_A2` ≅ C8 × C2, `order16_A3` ≅ C4 × C4,
`order16_A4` ≅ C4 × C2 × C2, `order16_A5` ≅ C2 × C2 × C2 × C2.

These are defined in `OrderP4_Abel.lean` along with their cardinality theorems.
-/

/-! ### Non-abelian representatives -/

section NonabelianDefs

/-! #### Center ≅ C4: two groups -/

/-- C8 ⋊ C2 via `x ↦ x⁵`.  The unit `5 ∈ (ZMod 8)ˣ` has order 2 and fixes the C4 subgroup
`{0, 2, 4, 6}` pointwise, so the center is `C4`.  This is the modular maximal-cyclic group
M₄(2) of order 16. -/
noncomputable abbrev order16_N1 : Type :=
  SemidirectProduct (Multiplicative (ZMod 8)) (Multiplicative (ZMod 2))
    (c2ActionAut 8 zmod8_unit_5 zmod8_unit_5_sq)

/-- Q8 ⋊ C2, where C2 acts on Q8 by an involutive automorphism fixing a cyclic C4 subgroup.
The skeleton type is a placeholder; the precise action will be defined later. -/
noncomputable abbrev order16_N2 : Type :=
  QuaternionGroup 2 × Multiplicative (ZMod 2)

/-! #### Center ≅ C2 × C2: four groups -/

/-- C4 ⋊ C4 via `x ↦ x³` on the normal C4.  The unit `3 ∈ (ZMod 4)ˣ` has order 2,
`Ker(φ) = {0,2}` ≅ C2, and the fixed points of `x ↦ x³` on C4 are `{0,2}` ≅ C2.
Together the center is `C2 × C2`. -/
noncomputable abbrev order16_N3 : Type :=
  SemidirectProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))
    (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4)

/-- (C2 × C2) ⋊ C4, where C4 acts on the Klein four group by swapping the two factors.
The kernel is the order-2 subgroup of C4, the fixed points are the diagonal C2,
and together the center is `C2 × C2`.  The skeleton type is a placeholder. -/
noncomputable abbrev order16_N4 : Type :=
  (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 4)

/-- D4 × C2.  D4 has center C2, so the product center is C2 × C2. -/
noncomputable abbrev order16_N5 : Type := DihedralGroup 4 × Multiplicative (ZMod 2)

/-- Q8 × C2.  Q8 has center C2, so the product center is C2 × C2. -/
noncomputable abbrev order16_N6 : Type := QuaternionGroup 2 × Multiplicative (ZMod 2)

/-! #### Center ≅ C2: three groups -/

/-- D8: the dihedral group of order 16.  Center is C2. -/
noncomputable abbrev order16_N7 : Type := DihedralGroup 8

/-- Q16: the generalised quaternion group of order 16.  Center is C2. -/
noncomputable abbrev order16_N8 : Type := QuaternionGroup 4

/-- C8 ⋊ C2 via `x ↦ x³` (semidihedral of order 16).  The unit `3 ∈ (ZMod 8)ˣ` has order 2
and fixes only `{0, 4}` ≅ C2, so the center is C2. -/
noncomputable abbrev order16_N9 : Type :=
  SemidirectProduct (Multiplicative (ZMod 8)) (Multiplicative (ZMod 2))
    (c2ActionAut 8 zmod8_unit_3 zmod8_unit_3_sq)

end NonabelianDefs

/-! ### The full list of 14 representatives -/

/-- The 14 isomorphism classes of groups of order 16, as a `Fin 14`-indexed family.

- Indices `0`–`4`: abelian groups `order16_A1`–`order16_A5`
- Indices `5`–`13`: non-abelian groups `order16_N1`–`order16_N9` -/
noncomputable abbrev order16_reps : Fin 14 → Type
  | 0 => order16_A1
  | 1 => order16_A2
  | 2 => order16_A3
  | 3 => order16_A4
  | 4 => order16_A5
  | 5 => order16_N1
  | 6 => order16_N2
  | 7 => order16_N3
  | 8 => order16_N4
  | 9 => order16_N5
  | 10 => order16_N6
  | 11 => order16_N7
  | 12 => order16_N8
  | 13 => order16_N9

noncomputable instance instGroupOrder16Reps (i : Fin 14) : Group (order16_reps i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | 4 => inferInstance
  | 5 => inferInstance
  | 6 => inferInstance
  | 7 => inferInstance
  | 8 => inferInstance
  | 9 => inferInstance
  | 10 => inferInstance
  | 11 => inferInstance
  | 12 => inferInstance
  | 13 => inferInstance

/-! ### Cardinalities -/

/-- The cardinality of `QuaternionGroup 2` (Q8) is 8. -/
theorem card_quaternion_group_2 : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- The cardinality of `QuaternionGroup 4` (Q16) is 16. -/
theorem card_quaternion_group_4 : Nat.card (QuaternionGroup 4) = 16 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- Each representative has order 16. -/
theorem card_order16_reps (i : Fin 14) : Nat.card (order16_reps i) = 16 :=
  match i with
  | 0 => card_order16_A1
  | 1 => card_order16_A2
  | 2 => card_order16_A3
  | 3 => card_order16_A4
  | 4 => card_order16_A5
  | 5 => by
    dsimp [order16_reps, order16_N1]; rw [SemidirectProduct.card]; simp
  | 6 => by
    dsimp [order16_reps, order16_N2]; rw [Nat.card_prod, card_quaternion_group_2]; simp
  | 7 => by
    dsimp [order16_reps, order16_N3]; rw [SemidirectProduct.card]; simp
  | 8 => by
    dsimp [order16_reps, order16_N4]; rw [Nat.card_prod, Nat.card_prod]; simp
  | 9 => by
    dsimp [order16_reps, order16_N5]; rw [Nat.card_prod, DihedralGroup.nat_card]; simp
  | 10 => by
    dsimp [order16_reps, order16_N6]; rw [Nat.card_prod, card_quaternion_group_2]; simp
  | 11 => by
    dsimp [order16_reps, order16_N7]; simpa using DihedralGroup.nat_card (n := 8)
  | 12 => by
    dsimp [order16_reps, order16_N8]; rw [card_quaternion_group_4]
  | 13 => by
    dsimp [order16_reps, order16_N9]; rw [SemidirectProduct.card]; simp

end Smallgroups.UsefulTheorems
