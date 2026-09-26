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
import Order16Library.UsefulTheorems.Counting
import Order16Library.UsefulTheorems.Order16
import Order16Library.UsefulTheorems.Order88
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement

/-!
# Classification of groups of order 16 via cyclic extensions (Wild 2005)

Following Marcel Wild's "The Groups of Order Sixteen Made Easy" (AMM, 2005),
we classify groups of order 16 using **cyclic extensions**.

## The key structural insight (Lemma 2 of Wild)

Every group G of order 16 not isomorphic to (C₂)⁴ has a normal subgroup
of order 8 isomorphic to C₈ or K₈ (= C₄ × C₂).  Thus G is built as an extension
(N, 2, τ, v) where τ ∈ Aut(N) with τ² = id, and v ∈ N satisfies τ(v) = v.

## The approach

1. **Lemma 2**: Every non-(C₂)⁴ group of order 16 has a normal C₈ or K₈.
2. **Extension type enumeration**: From Aut(C₈) ≅ K₄ (4 involutions) and
   Aut(K₈) ≅ D₈ (4 conjugacy classes of involutions), we get 6 + 7 = 13
   extension types, plus G₀ = (C₂)⁴.
3. **Realization and distinction**: Each type gives a concrete group;
   element orders and commutativity distinguish them.

## The 14 groups (Wild numbering)

- G₀ = (C₂)⁴ (the "outsider", all elements of order ≤ 2)
- G₁ = C₈ × C₂ … (C₈, 2, id, e)
- G₂ = SD₁₆ = C₈⋊₃C₂ … (C₈, 2, φ₂, e) — semidihedral
- G₃ = C₈⋊₅C₂ … (C₈, 2, φ₃, e)
- G₄ = D₁₆ = C₈⋊₇C₂ … (C₈, 2, φ₄, e) — dihedral
- G₅ = Q₁₆ … (C₈, 2, φ₄, x⁴) — generalized quaternion
- G₆ = C₁₆ … (C₈, 2, id, x) — cyclic
- G₇ = K₄ × C₄ … (K₈, 2, ψ₁, e)
- G₈ = D₈ × C₂ … (K₈, 2, ψ₃, e)
- G₉ = K₄⋊C₄ … (K₈, 2, ψ₅, e)
- G₁₀ = Q₈⋊C₂ … (K₈, 2, ψ₆, e)
- G₁₁ = Q₈ × C₂ … (K₈, 2, ψ₃, x²)
- G₁₂ = C₄⋊C₄ … (K₈, 2, ψ₅, x²)
- G₁₃ = C₄ × C₄ … (K₈, 2, ψ₁, y)

## Main results

* `lemma_normal_c8_or_k8` — Lemma 2: every non-(C₂)⁴ group of order 16 has a normal C₈ or K₈
* `order16_wild_reps` — the 14 concrete representatives
* `order16_wild_classification` — every group of order 16 is isomorphic to one of the 14
* `order16_wild_distinct` — the 14 are pairwise non-isomorphic
-/


namespace Smallgroups.UsefulTheorems

open SemidirectProduct
open Subgroup
open scoped Pointwise

/-! ### C₈ and K₈: type abbreviations and basic properties -/

/-- Cyclic group of order 8 (multiplicative). -/
abbrev C8g : Type := Multiplicative (ZMod 8)

/-- The Klein-8 group C₄ × C₂ ≅ `⟨x, y | x⁴ = y² = 1, xy = yx⟩`. -/
abbrev K8g : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)

instance : Group C8g := inferInstance
instance : Group K8g := inferInstance
instance : CommGroup C8g := inferInstance
instance : CommGroup K8g := inferInstance

@[simp] theorem card_C8g : Nat.card C8g = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

@[simp] theorem card_K8g : Nat.card K8g = 8 := by
  simp [K8g]

/-- Generator of C₈: `Multiplicative.ofAdd (1 : ZMod 8)`. -/
def xC8 : C8g := Multiplicative.ofAdd 1

theorem orderOf_xC8 : orderOf (xC8 : C8g) = 8 := by
  unfold xC8
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- Generators of K₈: `x` of order 4 and `y` of order 2, commuting. -/
def xK8 : K8g := (Multiplicative.ofAdd 1, 1)

def yK8 : K8g := (1, Multiplicative.ofAdd 1)

theorem orderOf_xK8 : orderOf (xK8 : K8g) = 4 := by
  dsimp [xK8]
  rw [Prod.orderOf_mk]
  have h1 : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have h2 : orderOf (1 : Multiplicative (ZMod 2)) = 1 := by simp
  rw [h1, h2]
  simp

theorem orderOf_yK8 : orderOf (yK8 : K8g) = 2 := by
  dsimp [yK8]
  rw [Prod.orderOf_mk]
  have h1 : orderOf (1 : Multiplicative (ZMod 4)) = 1 := by simp
  have h2 : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  rw [h1, h2]
  simp

theorem xK8_sq_ne_one : xK8 ^ 2 ≠ 1 := by
  have hord : orderOf (xK8 : K8g) = 4 := orderOf_xK8
  intro hsq
  have hsq' : (xK8 : K8g) ^ 2 = 1 := hsq
  have hdvd : orderOf (xK8 : K8g) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsq'
  rw [hord] at hdvd
  omega

/-! ### Automorphisms of C₈

`Aut(C₈) ≅ (Z/8Z)ˣ ≅ K₄`. The four involutive automorphisms
φ₁ (id), φ₂ (x ↦ x³), φ₃ (x ↦ x⁵), φ₄ (x ↦ x⁷)
correspond to multiplication by the units 1, 3, 5, 7 of Z/8Z.

We use `unitAut` and `zmod8_unit_*` from `Order16.lean`.
-/

def zmod8_unit_7 : (ZMod 8)ˣ :=
  ZMod.unitOfCoprime 7 (by norm_num)

@[simp] theorem zmod8_unit_7_sq : zmod8_unit_7 ^ 2 = 1 := by
  unfold zmod8_unit_7; decide

/-- The automorphism φ₂: x ↦ x³ on C₈. -/
noncomputable def phi2 : MulAut C8g := unitAut 8 zmod8_unit_3

/-- The automorphism φ₃: x ↦ x⁵ on C₈. -/
noncomputable def phi3 : MulAut C8g := unitAut 8 zmod8_unit_5

/-- The automorphism φ₄: x ↦ x⁷ on C₈ (inversion). -/
noncomputable def phi4 : MulAut C8g := unitAut 8 zmod8_unit_7

@[simp] theorem phi2_sq : phi2 ^ 2 = 1 := by
  unfold phi2; rw [← MonoidHom.map_pow, zmod8_unit_3_sq]; simp

@[simp] theorem phi3_sq : phi3 ^ 2 = 1 := by
  unfold phi3; rw [← MonoidHom.map_pow, zmod8_unit_5_sq]; simp

@[simp] theorem phi4_sq : phi4 ^ 2 = 1 := by
  unfold phi4; rw [← MonoidHom.map_pow, zmod8_unit_7_sq]; simp

/-! ### Automorphisms of K₈ (= C₄ × C₂)

`Aut(K₈) ≅ D₈`.  The eight automorphisms from Fact 4 of Wild.
Working multiplicatively on `K8g = Multiplicative (ZMod 4) × Multiplicative (ZMod 2)`,
the four involutive conjugacy classes are:

* ψ₁ = id:        (x, y) ↦ (x, y)
* ψ₃:             (x, y) ↦ (x⁻¹, y)
* ψ₅:             (x, y) ↦ (x, π(x) * y)  where π : C₄ → C₂ is the natural projection
* ψ₆:             (x, y) ↦ (x⁻¹ * ι(y), y)  where ι : C₂ → C₄ sends the generator to x²

All four satisfy ψ² = id.  The conjugacy classes of involutions in Aut(K₈) ≅ D₈ are
{ψ₁}, {ψ₃}, {ψ₅, ψ₇} and {ψ₆, ψ₈} (Wild, Fact 4), so ψ₁, ψ₃, ψ₅, ψ₆ are
representatives of the four classes.
-/

/-- The natural projection `Multiplicative (ZMod 4) → Multiplicative (ZMod 2)`
sending `ofAdd a` to `ofAdd (a mod 2)`. This is a group homomorphism. -/
noncomputable def k8Proj : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (ZMod.cast (Multiplicative.toAdd x) : ZMod 2)
  map_one' := by simp
  map_mul' x y := by
    simp [toAdd_mul, ZMod.cast_add]

theorem k8Proj_sq (x : Multiplicative (ZMod 4)) : (k8Proj x) ^ 2 = 1 := by
  have hcard : Fintype.card (Multiplicative (ZMod 2)) = 2 := by simp
  have h := pow_card_eq_one (x := k8Proj x)
  rw [hcard] at h
  exact h

/-- ψ₁ = identity on K₈. -/
def psi1 : MulAut K8g := MulEquiv.refl _

/-- ψ₃: x ↦ x⁻¹, y ↦ y.  Additively: (a,b) ↦ (-a, b). -/
noncomputable def psi3 : MulAut K8g where
  toFun p := (p.1⁻¹, p.2)
  invFun p := (p.1⁻¹, p.2)
  left_inv p := by rcases p with ⟨x, y⟩; simp
  right_inv p := by rcases p with ⟨x, y⟩; simp
  map_mul' p q := by
    rcases p with ⟨x₁, y₁⟩
    rcases q with ⟨x₂, y₂⟩
    simp [mul_inv_rev, mul_comm]

@[simp] theorem k8Proj_self_mul (x : Multiplicative (ZMod 4)) : k8Proj x * k8Proj x = 1 := by
  rw [← sq, k8Proj_sq x]

@[simp] theorem k8Proj_inv (x : Multiplicative (ZMod 4)) : (k8Proj x)⁻¹ = k8Proj x := by
  apply inv_eq_iff_mul_eq_one.mpr
  rw [k8Proj_self_mul x]

/-- ψ₅: x ↦ xy, y ↦ y.  Additively: (a,b) ↦ (a, c(a)+b). -/
noncomputable def psi5 : MulAut K8g where
  toFun p := (p.1, k8Proj p.1 * p.2)
  invFun p := (p.1, (k8Proj p.1)⁻¹ * p.2)
  left_inv p := by
    rcases p with ⟨x, y⟩; dsimp
    calc
      (x, (k8Proj x)⁻¹ * (k8Proj x * y)) = (x, ((k8Proj x)⁻¹ * k8Proj x) * y) := by group
      _ = (x, 1 * y) := by simp
      _ = (x, y) := by simp
  right_inv p := by
    rcases p with ⟨x, y⟩; dsimp
    calc
      (x, k8Proj x * ((k8Proj x)⁻¹ * y)) = (x, (k8Proj x * (k8Proj x)⁻¹) * y) := by group
      _ = (x, 1 * y) := by simp
      _ = (x, y) := by simp
  map_mul' p q := by
    rcases p with ⟨x₁, y₁⟩; rcases q with ⟨x₂, y₂⟩
    apply Prod.ext
    · rfl
    · simp [k8Proj.map_mul, mul_assoc, mul_left_comm, mul_comm]

/-- The embedding `Multiplicative (ZMod 2) →* Multiplicative (ZMod 4)`
sending `ofAdd b` to `ofAdd (2·b)`, i.e. the generator of C₂ to `x²`. -/
def k8Emb : Multiplicative (ZMod 2) →* Multiplicative (ZMod 4) where
  toFun y := Multiplicative.ofAdd (2 * (ZMod.cast (Multiplicative.toAdd y) : ZMod 4))
  map_one' := by decide
  map_mul' := by decide

/-- ψ₆: x ↦ x³, y ↦ x²y.  Additively: (a,b) ↦ (-a + 2b, b).

This is Wild's ψ₆ (Fact 4): a representative of the conjugacy class {ψ₆, ψ₈}
of involutions in Aut(K₈), the class *not* containing ψ₅. -/
def psi6 : MulAut K8g where
  toFun p := (p.1⁻¹ * k8Emb p.2, p.2)
  invFun p := (p.1⁻¹ * k8Emb p.2, p.2)
  left_inv p := by revert p; decide
  right_inv p := by revert p; decide
  map_mul' p q := by revert p q; decide

@[simp] theorem psi1_sq : psi1 ^ 2 = 1 := by
  unfold psi1; apply MulEquiv.ext; intro x; rfl

@[simp] theorem psi3_sq : psi3 ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  rcases p with ⟨x, y⟩
  calc
    (psi3 ^ 2) (x, y) = psi3 (psi3 (x, y)) := rfl
    _ = psi3 (x⁻¹, y) := rfl
    _ = ((x⁻¹)⁻¹, y) := rfl
    _ = (x, y) := by simp

@[simp] theorem psi5_sq : psi5 ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  rcases p with ⟨x, y⟩
  calc
    (psi5 ^ 2) (x, y) = psi5 (psi5 (x, y)) := rfl
    _ = psi5 (x, k8Proj x * y) := rfl
    _ = (x, k8Proj x * (k8Proj x * y)) := rfl
    _ = (x, (k8Proj x * k8Proj x) * y) := by group
    _ = (x, (k8Proj x ^ 2) * y) := by rw [sq]
    _ = (x, 1 * y) := by rw [k8Proj_sq x]
    _ = (x, y) := by simp

@[simp] theorem psi6_sq : psi6 ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  change psi6 (psi6 p) = p
  revert p; decide

/-! ### C₂ → Aut(N) maps for building semidirect products -/

private lemma c2_two_cases (a : Multiplicative (ZMod 2)) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

@[simp] private lemma c2_mul_self : (Multiplicative.ofAdd (1 : ZMod 2)
* Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 := by
  decide

set_option linter.flexible false in
/-- C₂-action on C₈ via φ₂ (x ↦ x³). -/
noncomputable def c2Action_phi2 : Multiplicative (ZMod 2) →* MulAut C8g where
  toFun g := if g = 1 then 1 else phi2
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, phi2_sq]

set_option linter.flexible false in
/-- C₂-action on C₈ via φ₃ (x ↦ x⁵). -/
noncomputable def c2Action_phi3 : Multiplicative (ZMod 2) →* MulAut C8g where
  toFun g := if g = 1 then 1 else phi3
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, phi3_sq]

set_option linter.flexible false in
/-- C₂-action on C₈ via φ₄ (x ↦ x⁷). -/
noncomputable def c2Action_phi4 : Multiplicative (ZMod 2) →* MulAut C8g where
  toFun g := if g = 1 then 1 else phi4
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, phi4_sq]

set_option linter.flexible false in
/-- C₂-action on K₈ via ψ₃. -/
noncomputable def c2Action_psi3 : Multiplicative (ZMod 2) →* MulAut K8g where
  toFun g := if g = 1 then 1 else psi3
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, psi3_sq]

set_option linter.flexible false in
/-- C₂-action on K₈ via ψ₅. -/
noncomputable def c2Action_psi5 : Multiplicative (ZMod 2) →* MulAut K8g where
  toFun g := if g = 1 then 1 else psi5
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, psi5_sq]

set_option linter.flexible false in
/-- C₂-action on K₈ via ψ₆. -/
noncomputable def c2Action_psi6 : Multiplicative (ZMod 2) →* MulAut K8g where
  toFun g := if g = 1 then 1 else psi6
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, psi6_sq]

/-! ### The 14 concrete groups

We define each group in order, matching the algebraic descriptions from Wild.

**Six groups from C₈-extensions:**
-/

/-- G₁ = C₈ × C₂. -/
noncomputable abbrev order16_wild_G1 : Type := C8g × Multiplicative (ZMod 2)

/-- G₂ = SD₁₆ = C₈ ⋊₃ C₂ (semidihedral). -/
noncomputable abbrev order16_wild_G2 : Type :=
  SemidirectProduct C8g (Multiplicative (ZMod 2)) c2Action_phi2

/-- G₃ = C₈ ⋊₅ C₂. -/
noncomputable abbrev order16_wild_G3 : Type :=
  SemidirectProduct C8g (Multiplicative (ZMod 2)) c2Action_phi3

/-- G₄ = D₁₆ = C₈ ⋊₇ C₂ (dihedral). -/
noncomputable abbrev order16_wild_G4 : Type :=
  SemidirectProduct C8g (Multiplicative (ZMod 2)) c2Action_phi4

/-- G₅ = Q₁₆ (generalized quaternion). -/
noncomputable abbrev order16_wild_G5 : Type := QuaternionGroup 4

/-- G₆ = C₁₆ (cyclic). -/
noncomputable abbrev order16_wild_G6 : Type := order16_A1

/-! **Seven groups from K₈-extensions:** -/

/-- G₇ = K₄ × C₄. -/
noncomputable abbrev order16_wild_G7 : Type := K8g × Multiplicative (ZMod 2)

/-- G₈ = D₈ × C₂. -/
noncomputable abbrev order16_wild_G8 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 2)) c2Action_psi3

/-- G₉ = K₄ ⋊ C₄. -/
noncomputable abbrev order16_wild_G9 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 2)) c2Action_psi5

/-- G₁₀ = Q₈ ⋊ C₂. -/
noncomputable abbrev order16_wild_G10 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 2)) c2Action_psi6

/-- G₁₁ = Q₈ × C₂. -/
noncomputable abbrev order16_wild_G11 : Type := QuaternionGroup 2 × Multiplicative (ZMod 2)

/-- G₁₂ = C₄ ⋊ C₄ (semidirect product of C₄ by C₄ via inversion `x ↦ x⁻¹`).
We reuse the definition from `Order16.lean`. -/
noncomputable abbrev order16_wild_G12 : Type := order16_N3

/-- G₁₃ = C₄ × C₄. -/
noncomputable abbrev order16_wild_G13 : Type := order16_A3

/-- G₀ = (C₂)⁴ (the "outsider"). -/
noncomputable abbrev order16_wild_G0 : Type := order16_A5

/-! ### Cardinalities -/

@[simp] theorem card_order16_wild_G0 : Nat.card order16_wild_G0 = 16 := card_order16_A5
@[simp] theorem card_order16_wild_G1 : Nat.card order16_wild_G1 = 16 := by simp
@[simp] theorem card_order16_wild_G2 : Nat.card order16_wild_G2 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G3 : Nat.card order16_wild_G3 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G4 : Nat.card order16_wild_G4 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G5 : Nat.card order16_wild_G5 = 16 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
@[simp] theorem card_order16_wild_G6 : Nat.card order16_wild_G6 = 16 := card_order16_A1
@[simp] theorem card_order16_wild_G7 : Nat.card order16_wild_G7 = 16 := by simp
@[simp] theorem card_order16_wild_G8 : Nat.card order16_wild_G8 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G9 : Nat.card order16_wild_G9 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G10 : Nat.card order16_wild_G10 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G11 : Nat.card order16_wild_G11 = 16 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]; simp
@[simp] theorem card_order16_wild_G12 : Nat.card order16_wild_G12 = 16 := by
  dsimp [order16_wild_G12, order16_N3]; rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G13 : Nat.card order16_wild_G13 = 16 := card_order16_A3

/-! ### The full list of 14 representatives -/

/-- The 14 isomorphism classes of groups of order 16 (Wild numbering). -/
noncomputable abbrev order16_wild_reps : Fin 14 → Type
  | 0 => order16_wild_G0
  | 1 => order16_wild_G1
  | 2 => order16_wild_G2
  | 3 => order16_wild_G3
  | 4 => order16_wild_G4
  | 5 => order16_wild_G5
  | 6 => order16_wild_G6
  | 7 => order16_wild_G7
  | 8 => order16_wild_G8
  | 9 => order16_wild_G9
  | 10 => order16_wild_G10
  | 11 => order16_wild_G11
  | 12 => order16_wild_G12
  | 13 => order16_wild_G13

noncomputable instance instGroupOrder16WildReps (i : Fin 14) : Group (order16_wild_reps i) :=
  match i with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
  | 8 => inferInstance | 9 => inferInstance | 10 => inferInstance | 11 => inferInstance
  | 12 => inferInstance | 13 => inferInstance

/-- Each representative has order 16. -/
theorem card_order16_wild_reps (i : Fin 14) : Nat.card (order16_wild_reps i) = 16 := by
  fin_cases i <;>
    first
    | exact card_order16_wild_G0
    | exact card_order16_wild_G1
    | exact card_order16_wild_G2
    | exact card_order16_wild_G3
    | exact card_order16_wild_G4
    | exact card_order16_wild_G5
    | exact card_order16_wild_G6
    | exact card_order16_wild_G7
    | exact card_order16_wild_G8
    | exact card_order16_wild_G9
    | exact card_order16_wild_G10
    | exact card_order16_wild_G11
    | exact card_order16_wild_G12
    | exact card_order16_wild_G13

/-! ### Concrete models of the abelian representatives

`order16_wild_G0/G6/G13` are `partitionGroup`s — Pi types indexed by `Multiset.toList` of the
partition, whose order is opaque.  Here we identify each of the five abelian representatives
with an explicit product of cyclic groups, which is needed both for counting invariants and
for the classification proof.
-/

section AbelianModels

private lemma exists_pair_of_length_two {l : List ℕ} (h : l.length = 2) :
    ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

private lemma exists_triple_of_length_three {l : List ℕ} (h : l.length = 3) :
    ∃ x y z, l = [x, y, z] := by
  match l, h with
  | [x, y, z], _ => exact ⟨x, y, z, rfl⟩

private lemma perm_pair {a b : ℕ} {l : List ℕ} (h : l.Perm [a, b]) :
    l = [a, b] ∨ l = [b, a] := by
  obtain ⟨x, y, rfl⟩ := exists_pair_of_length_two (by simpa using h.length_eq)
  have hx : x = a ∨ x = b := by
    have hmem := h.subset (show x ∈ [x, y] by simp)
    simpa using hmem
  rcases hx with rfl | rfl
  · have h' : [y].Perm [b] := h.cons_inv
    left
    rw [List.perm_singleton.mp h']
  · have h2 : [x, y].Perm [x, a] := h.trans (List.Perm.swap x a [])
    have h' : [y].Perm [a] := h2.cons_inv
    right
    rw [List.perm_singleton.mp h']

private lemma perm_triple_211 {l : List ℕ} (h : l.Perm [2, 1, 1]) :
    l = [2, 1, 1] ∨ l = [1, 2, 1] ∨ l = [1, 1, 2] := by
  obtain ⟨x, y, z, rfl⟩ := exists_triple_of_length_three (by simpa using h.length_eq)
  have hx : x = 2 ∨ x = 1 := by
    have hmem := h.subset (show x ∈ [x, y, z] by simp)
    simp at hmem
    tauto
  rcases hx with rfl | rfl
  · have h' : [y, z].Perm [1, 1] := h.cons_inv
    have h2 : [y, z] = [1, 1] := (perm_pair h').elim id id
    obtain ⟨rfl, rfl⟩ : y = 1 ∧ z = 1 := by simpa using h2
    left; rfl
  · have h' : [y, z].Perm [2, 1] := by
      have hh := (List.cons_perm_iff_perm_erase.mp h).2
      simpa using hh
    rcases perm_pair h' with h2 | h2
    · obtain ⟨rfl, rfl⟩ : y = 2 ∧ z = 1 := by simpa using h2
      right; left; rfl
    · obtain ⟨rfl, rfl⟩ : y = 1 ∧ z = 2 := by simpa using h2
      right; right; rfl

private lemma perm_ones {l : List ℕ} (h : l.Perm [1, 1, 1, 1]) : l = [1, 1, 1, 1] := by
  have hlen : l.length = 4 := by simpa using h.length_eq
  have hmem : ∀ x ∈ l, x = 1 := fun x hx => by
    have := h.subset hx
    simpa using this
  have hrep : l = List.replicate 4 1 := by
    rw [List.eq_replicate_iff]
    exact ⟨hlen, hmem⟩
  simpa using hrep

private lemma toList_perm (s : Multiset ℕ) (l : List ℕ) (h : s = ↑l) : s.toList.Perm l := by
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, h]

/-- A `MulEquiv` between Pi-type groups over equal lists. -/
private def listGroupCongr (p : ℕ) {l l' : List ℕ} (h : l = l') :
    ((i : Fin l.length) → Multiplicative (ZMod (p ^ l.get i))) ≃*
      ((i : Fin l'.length) → Multiplicative (ZMod (p ^ l'.get i))) := by
  cases h; exact MulEquiv.refl _

/-- Pi over `Fin 1` as a single factor, multiplicatively. -/
private def piFinOneMulEquiv (M : Fin 1 → Type*) [∀ i, Mul (M i)] :
    ((i : Fin 1) → M i) ≃* M 0 where
  toFun f := f 0
  invFun x := Fin.cons x finZeroElim
  left_inv f := by funext i; fin_cases i; rfl
  right_inv x := rfl
  map_mul' f g := rfl

/-- Pi over `Fin 2` as a binary product, multiplicatively. -/
private def piFinTwoMulEquiv (M : Fin 2 → Type*) [∀ i, Mul (M i)] :
    ((i : Fin 2) → M i) ≃* M 0 × M 1 :=
  { piFinTwoEquiv M with map_mul' := fun _ _ => rfl }

/-- Pi over `Fin 3` as an iterated product, multiplicatively. -/
private def piFinThreeMulEquiv (M : Fin 3 → Type*) [∀ i, Mul (M i)] :
    ((i : Fin 3) → M i) ≃* M 0 × M 1 × M 2 where
  toFun f := (f 0, f 1, f 2)
  invFun x := Fin.cons x.1 (Fin.cons x.2.1 (Fin.cons x.2.2 finZeroElim))
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv x := rfl
  map_mul' f g := rfl

/-- Pi over `Fin 4` as an iterated product, multiplicatively. -/
private def piFinFourMulEquiv (M : Fin 4 → Type*) [∀ i, Mul (M i)] :
    ((i : Fin 4) → M i) ≃* M 0 × M 1 × M 2 × M 3 where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun x := Fin.cons x.1 (Fin.cons x.2.1 (Fin.cons x.2.2.1 (Fin.cons x.2.2.2 finZeroElim)))
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv x := rfl
  map_mul' f g := rfl

/-- The elementary abelian model `(C₂)⁴` as an explicit product. -/
abbrev order16_wild_C2pow4 : Type :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ×
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

/-- `G₆ = order16_A1 ≅ C₁₆` concretely. -/
theorem order16_A1_iso_concrete :
    Nonempty (order16_A1 ≃* Multiplicative (ZMod 16)) := by
  have h : part4.parts.toList = [4] := List.perm_singleton.mp (toList_perm _ _ rfl)
  exact ⟨(listGroupCongr 2 h).trans <| (piFinOneMulEquiv _).trans
    (multZmodCongr (by norm_num))⟩

/-- `order16_A2 ≅ C₈ × C₂ = G₁` concretely. -/
theorem order16_A2_iso_concrete :
    Nonempty (order16_A2 ≃* C8g × Multiplicative (ZMod 2)) := by
  rcases perm_pair (toList_perm part31.parts [3, 1] rfl) with h | h
  · exact ⟨(listGroupCongr 2 h).trans <| (piFinTwoMulEquiv _).trans <|
      MulEquiv.prodCongr (multZmodCongr (by norm_num)) (multZmodCongr (by norm_num))⟩
  · exact ⟨(listGroupCongr 2 h).trans <| (piFinTwoMulEquiv _).trans <|
      (MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 1 = 2))
        (multZmodCongr (by norm_num : 2 ^ 3 = 8))).trans MulEquiv.prodComm⟩

/-- `G₁₃ = order16_A3 ≅ C₄ × C₄` concretely. -/
theorem order16_A3_iso_concrete :
    Nonempty (order16_A3 ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have h : part22.parts.toList = [2, 2] :=
    (perm_pair (toList_perm part22.parts [2, 2] rfl)).elim id id
  exact ⟨(listGroupCongr 2 h).trans <| (piFinTwoMulEquiv _).trans <|
    MulEquiv.prodCongr (multZmodCongr (by norm_num)) (multZmodCongr (by norm_num))⟩

/-- `order16_A4 ≅ K₈ × C₂ = G₇` concretely. -/
theorem order16_A4_iso_concrete :
    Nonempty (order16_A4 ≃* K8g × Multiplicative (ZMod 2)) := by
  rcases perm_triple_211 (toList_perm part211.parts [2, 1, 1] rfl) with h | h | h
  · -- [2,1,1] : C4 × (C2 × C2) → (C4 × C2) × C2
    exact ⟨(listGroupCongr 2 h).trans <| (piFinThreeMulEquiv _).trans <|
      (MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 2 = 4))
        (MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 1 = 2))
          (multZmodCongr (by norm_num : 2 ^ 1 = 2)))).trans MulEquiv.prodAssoc.symm⟩
  · -- [1,2,1] : C2 × (C4 × C2) → (C4 × C2) × C2
    exact ⟨(listGroupCongr 2 h).trans <| (piFinThreeMulEquiv _).trans <|
      (MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 1 = 2))
        (MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 2 = 4))
          (multZmodCongr (by norm_num : 2 ^ 1 = 2)))).trans MulEquiv.prodComm⟩
  · -- [1,1,2] : C2 × (C2 × C4) → C2 × (C4 × C2) → (C4 × C2) × C2
    exact ⟨(listGroupCongr 2 h).trans <| (piFinThreeMulEquiv _).trans <|
      ((MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 1 = 2))
        ((MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 1 = 2))
          (multZmodCongr (by norm_num : 2 ^ 2 = 4))).trans MulEquiv.prodComm)).trans
            MulEquiv.prodComm)⟩

/-- `G₀ = order16_A5 ≅ (C₂)⁴` concretely. -/
theorem order16_A5_iso_concrete :
    Nonempty (order16_A5 ≃* order16_wild_C2pow4) := by
  have h : part1111.parts.toList = [1, 1, 1, 1] :=
    perm_ones (toList_perm part1111.parts [1, 1, 1, 1] rfl)
  exact ⟨(listGroupCongr 2 h).trans <| (piFinFourMulEquiv _).trans <|
    MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 1 = 2)) <|
      MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 1 = 2)) <|
        MulEquiv.prodCongr (multZmodCongr (by norm_num : 2 ^ 1 = 2))
          (multZmodCongr (by norm_num : 2 ^ 1 = 2))⟩

end AbelianModels

/-! ### Auxiliary lemmas for Lemma 2 -/

/-- A group in which every element squares to `1` is commutative (Fact 2 of Wild). -/
private lemma mul_comm_of_sq_eq_one {G : Type*} [Group G]
    (h : ∀ g : G, g ^ 2 = 1) (a b : G) : a * b = b * a := by
  have ha_sq' : a * a = 1 := by rw [← pow_two]; exact h a
  have hb_sq' : b * b = 1 := by rw [← pow_two]; exact h b
  have hab_sq' : (a * b) * (a * b) = 1 := by rw [← pow_two]; exact h (a * b)
  have ha_inv : a = a⁻¹ := eq_inv_of_mul_eq_one_left ha_sq'
  have hb_inv : b = b⁻¹ := eq_inv_of_mul_eq_one_left hb_sq'
  have hab_inv : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab_sq'
  calc
    a * b = (a * b)⁻¹ := hab_inv
    _ = b⁻¹ * a⁻¹ := by simp
    _ = b * a := by rw [ha_inv.symm, hb_inv.symm]

/-- In a group of order `16` without elements of order `8`, every element has order
`1`, `2`, or `4`. -/
private lemma orderOf_cases_of_card16 {G : Type*} [Group G]
    (hcard : Nat.card G = 16) (h_ord8 : ¬ ∃ g : G, orderOf g = 8) (g : G) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 4 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : orderOf g ∣ 16 := by rw [← hcard]; exact orderOf_dvd_natCard g
  have h_not8 : orderOf g ≠ 8 := fun h => h_ord8 ⟨g, h⟩
  have h_not16 : orderOf g ≠ 16 := by
    intro h16
    exact h_ord8 ⟨g ^ 2, by rw [orderOf_pow g, h16]; norm_num⟩
  have h_mem : orderOf g ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h_divs : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
  rw [h_divs] at h_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
  omega

/-- Reduce an integer power of a torsion element to a natural power below the torsion bound. -/
private lemma zpow_eq_pow_emod {G : Type*} [Group G] (g : G) {n : ℕ} (hn : 0 < n)
    (hg : g ^ n = 1) (k : ℤ) : g ^ k = g ^ (k % (n : ℤ)).toNat := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 : (0 : ℤ) ≤ k % (n : ℤ) := Int.emod_nonneg k hn'
  calc g ^ k = g ^ ((n : ℤ) * (k / (n : ℤ)) + k % (n : ℤ)) := by
        rw [Int.mul_ediv_add_emod]
    _ = (g ^ (n : ℤ)) ^ (k / (n : ℤ)) * g ^ (k % (n : ℤ)) := by
        rw [zpow_add, zpow_mul]
    _ = g ^ (k % (n : ℤ)) := by
        rw [zpow_natCast, hg, one_zpow, one_mul]
    _ = g ^ (k % (n : ℤ)).toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg h0]

/-- An element of `⟨x⟩` is a natural power `x ^ m` with `m < orderOf x`. -/
private lemma exists_pow_eq_of_mem_zpowers {G : Type*} [Group G] {x y : G}
    (hx : 0 < orderOf x) (h : y ∈ Subgroup.zpowers x) :
    ∃ m : ℕ, m < orderOf x ∧ x ^ m = y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine ⟨(k % (orderOf x : ℤ)).toNat, ?_, ?_⟩
  · have hlt : k % (orderOf x : ℤ) < (orderOf x : ℤ) :=
      Int.emod_lt_of_pos k (by exact_mod_cast hx)
    have h0 : (0 : ℤ) ≤ k % (orderOf x : ℤ) :=
      Int.emod_nonneg k (by exact_mod_cast hx.ne')
    omega
  · rw [← zpow_eq_pow_emod x hx (pow_orderOf_eq_one x) k, hk]

/-- The homomorphism `Multiplicative (ZMod n) →* G` sending `Multiplicative.ofAdd 1` to `g`,
for an element `g` with `g ^ n = 1`. -/
private noncomputable def zmodPowHom {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift n
    ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_natCast, hg, ofMul_one]⟩

private lemma zmodPowHom_apply {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1)
    (k : ℕ) : zmodPowHom n g hg (Multiplicative.ofAdd ((k : ZMod n))) = g ^ k := by
  have h1 : (((k : ℤ)) : ZMod n) = ((k : ZMod n)) := by push_cast; rfl
  simp only [zmodPowHom, AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd]
  rw [← h1, ZMod.lift_coe]
  rw [zmultiplesHom_apply, ← ofMul_zpow, toMul_ofMul, zpow_natCast]

/-- If `x` has order `4`, `w` has order `2`, `x` and `w` commute, and `w ∉ ⟨x⟩`, then in a
group of order `16` the subgroup generated by `x` and `w` is a normal subgroup of order `8`
isomorphic to `K₈ = C₄ × C₂`. -/
private lemma normal_k8_of_commuting {G : Type*} [Group G] (hcard : Nat.card G = 16)
    (x w : G) (hx4 : orderOf x = 4) (hw2 : orderOf w = 2)
    (hcomm : Commute x w) (hw_notin : w ∉ Subgroup.zpowers x) :
    ∃ H : Subgroup G, H.Normal ∧ Nat.card H = 8 ∧ Nonempty (H ≃* K8g) := by
  classical
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hw2' : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  let fx : Multiplicative (ZMod 4) →* G := zmodPowHom 4 x hx4'
  let fw : Multiplicative (ZMod 2) →* G := zmodPowHom 2 w hw2'
  have hfx : ∀ a : Multiplicative (ZMod 4), fx a = x ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    conv_lhs => rw [ha]
    exact zmodPowHom_apply 4 x hx4' _
  have hfw : ∀ b : Multiplicative (ZMod 2), fw b = w ^ (Multiplicative.toAdd b).val := by
    intro b
    have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 2)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    conv_lhs => rw [hb]
    exact zmodPowHom_apply 2 w hw2' _
  have hcomm' : ∀ (a : Multiplicative (ZMod 4)) (b : Multiplicative (ZMod 2)),
      Commute (fx a) (fw b) := by
    intro a b
    rw [hfx a, hfw b]
    exact hcomm.pow_pow _ _
  have hinj : Function.Injective (fx.noncommCoprod fw hcomm') := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro ⟨a, b⟩ hab
    simp only [MonoidHom.noncommCoprod_apply] at hab
    rw [hfx a, hfw b] at hab
    have hbv_lt : (Multiplicative.toAdd b).val < 2 := ZMod.val_lt _
    have hav_lt : (Multiplicative.toAdd a).val < 4 := ZMod.val_lt _
    have hbv0 : (Multiplicative.toAdd b).val = 0 := by
      by_contra hbv1
      have hbv1' : (Multiplicative.toAdd b).val = 1 := by omega
      rw [hbv1', pow_one] at hab
      refine hw_notin ?_
      have hw_eq : w = (x ^ (Multiplicative.toAdd a).val)⁻¹ :=
        eq_inv_of_mul_eq_one_right hab
      rw [hw_eq]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
    rw [hbv0, pow_zero, mul_one] at hab
    have hav0 : (Multiplicative.toAdd a).val = 0 := by
      have hdvd : orderOf x ∣ (Multiplicative.toAdd a).val :=
        orderOf_dvd_of_pow_eq_one hab
      rw [hx4] at hdvd
      omega
    have ha1 : a = 1 := by
      have h0 : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).mp hav0
      rw [← ofAdd_toAdd a, h0, ofAdd_zero]
    have hb1 : b = 1 := by
      have h0 : Multiplicative.toAdd b = 0 := (ZMod.val_eq_zero _).mp hbv0
      rw [← ofAdd_toAdd b, h0, ofAdd_zero]
    rw [ha1, hb1]
    rfl
  have e : K8g ≃* (fx.noncommCoprod fw hcomm').range := MonoidHom.ofInjective hinj
  have hcardH : Nat.card (fx.noncommCoprod fw hcomm').range = 8 := by
    rw [← Nat.card_congr e.toEquiv]
    exact card_K8g
  have hidx : (fx.noncommCoprod fw hcomm').range.index = 2 := by
    have hmul := (fx.noncommCoprod fw hcomm').range.card_mul_index
    rw [hcardH, hcard] at hmul
    omega
  exact ⟨(fx.noncommCoprod fw hcomm').range, normal_of_index_eq_two hidx, hcardH, ⟨e.symm⟩⟩

/-- If a partition of `4` has a part `m ≥ 2`, then `partitionGroup 2 lam` has an element
whose square is nontrivial. -/
private lemma partitionGroup_sq_ne_one {a : ℕ} (lam : Nat.Partition a)
    {m : ℕ} (hm : 2 ≤ m) (hmem : m ∈ lam.parts) :
    ∃ g : partitionGroup 2 lam, g ^ 2 ≠ 1 := by
  classical
  have hmem' : m ∈ lam.parts.toList := Multiset.mem_toList.mpr hmem
  obtain ⟨j, hj_lt, hj⟩ := List.mem_iff_getElem.mp hmem'
  refine ⟨Pi.mulSingle ⟨j, hj_lt⟩
    (Multiplicative.ofAdd (1 : ZMod (2 ^ lam.parts.toList.get ⟨j, hj_lt⟩))), fun h => ?_⟩
  have hj2 := congrFun h ⟨j, hj_lt⟩
  rw [Pi.pow_apply, Pi.mulSingle_eq_same, Pi.one_apply] at hj2
  have hdvd := orderOf_dvd_of_pow_eq_one hj2
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one] at hdvd
  have hget : lam.parts.toList.get ⟨j, hj_lt⟩ = m := hj
  rw [hget] at hdvd
  have hle : 2 ^ m ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 4 ≤ 2 ^ m := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

/-! ### Lemma 2: Every non-(C₂)⁴ group of order 16 has a normal C₈ or K₈ -/

/-- Lemma 2 of Wild:
If G is a group of order 16 not isomorphic to (C₂)⁴, then G has a normal subgroup
of order 8 isomorphic to C₈ or to K₈. -/
theorem lemma_normal_c8_or_k8 {G : Type*} [Group G]
    (hcard : Nat.card G = 16)
    (h_not_elem : ¬ Nonempty (G ≃* order16_wild_G0)) :
    (∃ (H : Subgroup G), H.Normal ∧ Nat.card H = 8 ∧
      Nonempty (H ≃* C8g)) ∨
    (∃ (H : Subgroup G), H.Normal ∧ Nat.card H = 8 ∧
      Nonempty (H ≃* K8g)) := by
  classical
  have hcard' : Nat.card G ≠ 0 := by rw [hcard]; norm_num
  haveI : Finite G := by
    by_contra hinf
    haveI : Infinite G := ⟨hinf⟩
    have hcard0 : Nat.card G = 0 := Nat.card_eq_zero_of_infinite
    exact hcard' hcard0
  haveI : Fintype G := Fintype.ofFinite G
  -- If G has an element of order 8, then H = ⟨x⟩ ≅ C₈ is normal (index 2).
  by_cases h_ord8 : ∃ g : G, orderOf g = 8
  · rcases h_ord8 with ⟨g, hg⟩
    let H : Subgroup G := zpowers g
    have hHcard : Nat.card H = 8 := by rw [Nat.card_zpowers, hg]
    have hHindex : H.index = 2 := by
      have hmul := H.card_mul_index
      rw [hHcard, hcard] at hmul
      omega
    have hHnorm : H.Normal := normal_of_index_eq_two hHindex
    haveI : IsCyclic H := isCyclic_zpowers g
    have hH_iso : Nonempty (H ≃* C8g) :=
      cyclicRep_classification (by norm_num : (8 : ℕ) ≠ 0) hHcard
    exact Or.inl ⟨H, hHnorm, hHcard, hH_iso⟩
  · -- No element of order 8.
    -- Find an element z of order 2 in the center Z(G).
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard_pow : Nat.card G = 2 ^ 4 := by rw [hcard]; norm_num
    have h_center_nontriv : Nontrivial (Subgroup.center G) :=
      center_nontrivial_of_card_prime_pow hcard_pow (by norm_num : (0 : ℕ) < 4)
    haveI hc_nontriv : Nontrivial (Subgroup.center G) := h_center_nontriv
    obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center G)
    have hw_ne_one : (w : G) ≠ 1 := Subtype.coe_inj.not.mpr hw
    have hcard_fin : Fintype.card G = 16 := by
      rw [Fintype.card_eq_nat_card, hcard]
    have hw_order_dvd : orderOf (w : G) ∣ 16 := by
      rw [← hcard_fin]; exact orderOf_dvd_card
    have hw_order_not8 : orderOf (w : G) ≠ 8 := by
      intro h; apply h_ord8; exact ⟨(w : G), h⟩
    -- orderOf w ∈ {1,2,4}. Not 1 (nontrivial), not 8 (by assumption).
    have hw_order_24 : orderOf (w : G) = 2 ∨ orderOf (w : G) = 4 := by
      have hpos : 0 < orderOf (w : G) := orderOf_pos _
      have h_not1 : orderOf (w : G) ≠ 1 := by
        intro h1; apply hw_ne_one; exact (orderOf_eq_one_iff.mp h1)
      have h_not16 : orderOf (w : G) ≠ 16 := by
        intro h16
        have h8 : orderOf ((w : G) ^ 2) = 8 := by
          rw [orderOf_pow (w : G), h16]
          norm_num
        apply h_ord8
        exact ⟨(w : G) ^ 2, h8⟩
      have h_all_divs : (Nat.divisors 16) = {1,2,4,8,16} := by decide
      have h_mem : orderOf (w : G) ∈ Nat.divisors 16 :=
        Nat.mem_divisors.mpr ⟨hw_order_dvd, by norm_num⟩
      rw [h_all_divs] at h_mem
      have h_cases : orderOf (w : G) = 2 ∨ orderOf (w : G) = 4 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
        rcases h_mem with (h1 | h2 | h4 | h8 | h16)
        · exact (h_not1 h1).elim
        · left; exact h2
        · right; exact h4
        · exact (hw_order_not8 h8).elim
        · exact (h_not16 h16).elim
      exact h_cases
    -- Obtain nontrivial z ∈ Z(G) with orderOf z = 2
    have h_exists_z2 : ∃ z : G, z ∈ Subgroup.center G ∧ orderOf z = 2 := by
      rcases hw_order_24 with (hw2 | hw4)
      · exact ⟨(w : G), w.property, hw2⟩
      · refine ⟨(w : G) ^ 2, Subgroup.pow_mem _ w.property 2, ?_⟩
        rw [orderOf_pow (w : G), hw4]
        norm_num
    obtain ⟨z, hz_cent, hz_order2⟩ := h_exists_z2
    have hz_ne_one : z ≠ 1 := by
      intro h; rw [h, orderOf_one] at hz_order2; omega
    -- Now z is a central element of order 2.  Continue with Wild's case analysis.
    -- By Fact 2 (all elements squared = 1 ⇒ abelian), since G ≄ (C₂)⁴, there exists
    -- an element of order 4.  Otherwise G would be abelian exponent 2, hence ≅ (C₂)⁴.
    have h_exists_ord4 : ∃ x : G, orderOf x = 4 := by
      by_contra! h_no4
      -- If no element of order 4, then every element squares to 1.
      have h_all_sq_one : ∀ g : G, g ^ 2 = 1 := by
        intro g
        have hord : orderOf g = 1 ∨ orderOf g = 2 := by
          have hpos : 0 < orderOf g := orderOf_pos _
          have h_dvd : orderOf g ∣ 16 := by
            rw [← hcard_fin]; exact orderOf_dvd_card
          have h_not8 : orderOf g ≠ 8 := by
            intro h; apply h_ord8; exact ⟨g, h⟩
          have h_not16 : orderOf g ≠ 16 := by
            intro h16
            have h8 : orderOf (g ^ 2) = 8 := by
              rw [orderOf_pow g, h16]; norm_num
            apply h_ord8; exact ⟨g ^ 2, h8⟩
          have h_not4 : orderOf g ≠ 4 := h_no4 g
          have h_mem : orderOf g ∈ Nat.divisors 16 :=
            Nat.mem_divisors.mpr ⟨h_dvd, by norm_num⟩
          have h_divs : (Nat.divisors 16) = {1,2,4,8,16} := by decide
          rw [h_divs] at h_mem
          simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
          rcases h_mem with (h1 | h2' | h4 | h8 | h16)
          · left; exact h1
          · right; exact h2'
          · exact (h_not4 h4).elim
          · exact (h_not8 h8).elim
          · exact (h_not16 h16).elim
        rcases hord with (h1 | h2')
        · have hg1 : g = 1 := orderOf_eq_one_iff.mp h1
          rw [hg1, one_pow]
        · have htemp := pow_orderOf_eq_one g
          rw [h2'] at htemp; exact htemp
      have h_abel : ∀ a b : G, a * b = b * a := mul_comm_of_sq_eq_one h_all_sq_one
      -- G is abelian of order 2⁴ and exponent 2, hence ≅ (C₂)⁴ = G₀, contradicting h_not_elem
      letI : CommGroup G := { ‹Group G› with mul_comm := h_abel }
      have hcontra : ∀ (lam : Nat.Partition 4) (m : ℕ), 2 ≤ m → m ∈ lam.parts →
          (G ≃* partitionGroup 2 lam) → False := by
        intro lam m hm hmem e
        obtain ⟨g, hg⟩ := partitionGroup_sq_ne_one lam hm hmem
        apply hg
        calc g ^ 2 = e (e.symm g) ^ 2 := by rw [MulEquiv.apply_symm_apply]
          _ = e (e.symm g ^ 2) := (map_pow e _ 2).symm
          _ = e 1 := by rw [h_all_sq_one (e.symm g)]
          _ = 1 := map_one e
      obtain ⟨i, ⟨e⟩⟩ := orderP4Abel_complete 2 G (by rw [hcard]; norm_num)
      fin_cases i
      · exact hcontra part4 4 (by norm_num) (by decide) e
      · exact hcontra part31 3 (by norm_num) (by decide) e
      · exact hcontra part22 2 (by norm_num) (by decide) e
      · exact hcontra part211 2 (by norm_num) (by decide) e
      · exact h_not_elem ⟨e⟩
    obtain ⟨x, hx_order4⟩ := h_exists_ord4
    have hz2 : z ^ 2 = 1 := by
      have htemp := pow_orderOf_eq_one z
      rw [hz_order2] at htemp; exact htemp
    have hOrders : ∀ g : G, orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 4 :=
      orderOf_cases_of_card16 hcard h_ord8
    by_cases hsq_all : ∀ u : G, orderOf u = 4 → u ^ 2 = z
    · -- Case 2 of Wild: every element of order 4 squares to z.
      -- Then G/⟨z⟩ has exponent 2, hence is abelian, so the conjugacy class of x is
      -- contained in {x, zx}; the centralizer of x has order ≥ 8 and yields an element
      -- y ∉ ⟨x⟩ commuting with x, from which we build a normal K₈.
      have hx2z : x ^ 2 = z := hsq_all x hx_order4
      have hN_norm : (Subgroup.zpowers z).Normal := by
        constructor
        intro n hn g
        have hcn : ∀ h : G, h * n = n * h :=
          Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hz_cent) hn)
        have hfix : g * n * g⁻¹ = n := by rw [hcn g]; group
        rw [hfix]; exact hn
      haveI := hN_norm
      have hN_two : ∀ n : G, n ∈ Subgroup.zpowers z → n = 1 ∨ n = z := by
        intro n hn
        obtain ⟨m, hm_lt, hm⟩ :=
          exists_pow_eq_of_mem_zpowers (by rw [hz_order2]; norm_num) hn
        rw [hz_order2] at hm_lt
        interval_cases m
        · left; rw [← hm, pow_zero]
        · right; rw [← hm, pow_one]
      -- The quotient G/⟨z⟩ has exponent 2, hence is abelian
      have hquot_sq : ∀ q : G ⧸ Subgroup.zpowers z, q ^ 2 = 1 := by
        intro q
        refine QuotientGroup.induction_on q ?_
        intro g
        have hg2 : g * g ∈ Subgroup.zpowers z := by
          rw [← pow_two]
          rcases hOrders g with h1 | h2 | h4
          · rw [orderOf_eq_one_iff.mp h1, one_pow]; exact Subgroup.one_mem _
          · have := pow_orderOf_eq_one g
            rw [h2] at this
            rw [this]; exact Subgroup.one_mem _
          · rw [hsq_all g h4]; exact Subgroup.mem_zpowers z
        rw [pow_two, ← QuotientGroup.mk_mul]
        exact (QuotientGroup.eq_one_iff _).mpr hg2
      have hquot_comm : ∀ a b : G ⧸ Subgroup.zpowers z, a * b = b * a :=
        mul_comm_of_sq_eq_one hquot_sq
      -- Every conjugate of x lies in the coset {x, zx}
      have hconj_mem : ∀ g : G, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.zpowers z := by
        intro g
        rw [← QuotientGroup.eq_one_iff]
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        rw [hquot_comm (g : G ⧸ Subgroup.zpowers z) (x : G ⧸ Subgroup.zpowers z)]
        group
      have hconj_cases : ∀ g : G, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = z * x := by
        intro g
        rcases hN_two _ (hconj_mem g) with h1 | h1
        · left
          have h2 : g * x * g⁻¹ * x⁻¹ * x = 1 * x := by rw [h1]
          simpa using h2
        · right
          have h2 : g * x * g⁻¹ * x⁻¹ * x = z * x := by rw [h1]
          simpa using h2
      -- Orbit–stabilizer: the centralizer of x has at least 8 elements
      have horb_le : Nat.card (MulAction.orbit (ConjAct G) x) ≤ 2 := by
        have hsub : MulAction.orbit (ConjAct G) x ⊆ ({x, z * x} : Set G) := by
          rintro u ⟨h, rfl⟩
          simp only [ConjAct.smul_def, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact hconj_cases (ConjAct.ofConjAct h)
        calc Nat.card (MulAction.orbit (ConjAct G) x)
            = (MulAction.orbit (ConjAct G) x).ncard := Nat.card_coe_set_eq _
          _ ≤ ({x, z * x} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ ({z * x} : Set G).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      have hcardS : 8 ≤ Nat.card (MulAction.stabilizer (ConjAct G) x) := by
        have hprod := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct G) x)
        have hcardCG : Nat.card (ConjAct G) = 16 := by
          rw [← hcard]
          exact Nat.card_congr ConjAct.ofConjAct.toEquiv
        rw [hcardCG] at hprod
        have hidx_le : (MulAction.stabilizer (ConjAct G) x).index ≤ 2 := by
          have hindex_eq : (MulAction.stabilizer (ConjAct G) x).index
              = Nat.card (MulAction.orbit (ConjAct G) x) := by
            rw [Subgroup.index_eq_card]
            exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) x)).symm
          rw [hindex_eq]
          exact horb_le
        have h012 : (MulAction.stabilizer (ConjAct G) x).index = 0 ∨
            (MulAction.stabilizer (ConjAct G) x).index = 1 ∨
            (MulAction.stabilizer (ConjAct G) x).index = 2 := by omega
        rcases h012 with h | h | h <;> rw [h] at hprod <;> omega
      -- The powers of x form a subgroup of order 4 inside the stabilizer
      have hT_le : Subgroup.zpowers (ConjAct.toConjAct x) ≤
          MulAction.stabilizer (ConjAct G) x := by
        rw [Subgroup.zpowers_le]
        rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
        group
      have hcardT : Nat.card (Subgroup.zpowers (ConjAct.toConjAct x)) = 4 := by
        rw [Nat.card_zpowers,
          show ConjAct.toConjAct x = ConjAct.toConjAct.toMonoidHom x from rfl,
          orderOf_injective ConjAct.toConjAct.toMonoidHom ConjAct.toConjAct.injective,
          hx_order4]
      have hnotle : ¬ (MulAction.stabilizer (ConjAct G) x ≤
          Subgroup.zpowers (ConjAct.toConjAct x)) := by
        intro hle
        have hle_card := Subgroup.card_le_of_le hle
        omega
      obtain ⟨hc, hhS, hhT⟩ := SetLike.not_le_iff_exists.mp hnotle
      -- y := ofConjAct hc commutes with x and lies outside ⟨x⟩
      have hyx : ConjAct.ofConjAct hc * x * (ConjAct.ofConjAct hc)⁻¹ = x := by
        have hs := MulAction.mem_stabilizer_iff.mp hhS
        rwa [ConjAct.smul_def] at hs
      have hxy_comm : Commute x (ConjAct.ofConjAct hc) := by
        have h1 : ConjAct.ofConjAct hc * x = x * ConjAct.ofConjAct hc := by
          calc ConjAct.ofConjAct hc * x
              = (ConjAct.ofConjAct hc * x * (ConjAct.ofConjAct hc)⁻¹) *
                ConjAct.ofConjAct hc := by group
            _ = x * ConjAct.ofConjAct hc := by rw [hyx]
        exact h1.symm
      have hy_notin : ConjAct.ofConjAct hc ∉ Subgroup.zpowers x := by
        intro hmem
        apply hhT
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hk' : (ConjAct.toConjAct x) ^ k = hc := by
          rw [show ConjAct.toConjAct x = ConjAct.toConjAct.toMonoidHom x from rfl,
            ← map_zpow, hk]
          exact ConjAct.toConjAct_ofConjAct hc
        rw [← hk']
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
      rcases hOrders (ConjAct.ofConjAct hc) with hy1 | hy2 | hy4
      · exfalso
        apply hy_notin
        rw [orderOf_eq_one_iff.mp hy1]
        exact Subgroup.one_mem _
      · -- y has order 2: ⟨x, y⟩ is a normal K₈
        obtain ⟨H, hH1, hH2, hH3⟩ := normal_k8_of_commuting hcard x
          (ConjAct.ofConjAct hc) hx_order4 hy2 hxy_comm hy_notin
        exact Or.inr ⟨H, hH1, hH2, hH3⟩
      · -- y has order 4: then y² = z, so xy has order 2 and ⟨x, xy⟩ is a normal K₈
        have hy2z : (ConjAct.ofConjAct hc) ^ 2 = z := hsq_all _ hy4
        have hxy_sq : (x * ConjAct.ofConjAct hc) ^ 2 = 1 := by
          have hstep : (x * ConjAct.ofConjAct hc) ^ 2 =
              x ^ 2 * (ConjAct.ofConjAct hc) ^ 2 := by
            calc (x * ConjAct.ofConjAct hc) ^ 2
                = x * (ConjAct.ofConjAct hc * x) * ConjAct.ofConjAct hc := by
                  rw [pow_two]; group
              _ = x * (x * ConjAct.ofConjAct hc) * ConjAct.ofConjAct hc := by
                  rw [← hxy_comm.eq]
              _ = x ^ 2 * (ConjAct.ofConjAct hc) ^ 2 := by
                  rw [pow_two, pow_two]; group
          rw [hstep, hx2z, hy2z, ← pow_two, hz2]
        have hxy_ne : x * ConjAct.ofConjAct hc ≠ 1 := by
          intro h1
          apply hy_notin
          have h2 : ConjAct.ofConjAct hc = x⁻¹ := eq_inv_of_mul_eq_one_right h1
          rw [h2]
          exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
        have hxy_ord : orderOf (x * ConjAct.ofConjAct hc) = 2 :=
          orderOf_eq_prime hxy_sq hxy_ne
        have hxy_comm' : Commute x (x * ConjAct.ofConjAct hc) :=
          (Commute.refl x).mul_right hxy_comm
        have hxy_notin : x * ConjAct.ofConjAct hc ∉ Subgroup.zpowers x := by
          intro hmem
          apply hy_notin
          have h2 : ConjAct.ofConjAct hc = x⁻¹ * (x * ConjAct.ofConjAct hc) := by group
          rw [h2]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) hmem
        obtain ⟨H, hH1, hH2, hH3⟩ := normal_k8_of_commuting hcard x
          (x * ConjAct.ofConjAct hc) hx_order4 hxy_ord hxy_comm' hxy_notin
        exact Or.inr ⟨H, hH1, hH2, hH3⟩
    · -- Case 1 of Wild: some element u of order 4 has u² ≠ z; then ⟨u, z⟩ ≅ K₈
      push Not at hsq_all
      obtain ⟨u, hu4, husq⟩ := hsq_all
      have hu_comm : Commute u z := Subgroup.mem_center_iff.mp hz_cent u
      have hz_notin : z ∉ Subgroup.zpowers u := by
        intro hmem
        obtain ⟨m, hm_lt, hm⟩ :=
          exists_pow_eq_of_mem_zpowers (by rw [hu4]; norm_num) hmem
        rw [hu4] at hm_lt
        interval_cases m
        · rw [pow_zero] at hm; exact hz_ne_one hm.symm
        · rw [pow_one] at hm
          rw [hm] at hu4
          omega
        · exact husq hm
        · have hord3 : orderOf (u ^ 3) = 4 := by
            rw [orderOf_pow u, hu4]
            norm_num
          rw [hm, hz_order2] at hord3
          omega
      obtain ⟨H, hH1, hH2, hH3⟩ :=
        normal_k8_of_commuting hcard u z hu4 hz_order2 hu_comm hz_notin
      exact Or.inr ⟨H, hH1, hH2, hH3⟩

/-! ### Isomorphism invariants of the 14 representatives

For distinctness we use the invariant tuple
`(|Z(G)|, #{x : x² = 1}, #{x : x⁴ = 1}, #{squares})`,
whose values are pairwise distinct across the 14 representatives.  All counts on the
concrete (computable) models are established by kernel reduction; the three
`partitionGroup`-based representatives are transported through their concrete models.
-/

section Invariants

private theorem nat_card_eq_of_fintype_card_eq {α : Type*} [Fintype α] {n : Nat}
    (h : Fintype.card α = n) : Nat.card α = n :=
  Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq h)

/-- The number of squares in a group — an isomorphism invariant. -/
noncomputable def sq_image_card (H : Type*) [Group H] : ℕ :=
  Nat.card {y : H // ∃ x : H, x ^ 2 = y}

theorem sq_image_card_eq_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    sq_image_card H = sq_image_card K := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, by rw [← map_pow]; rfl⟩
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, e.injective ?_⟩
    rw [map_pow, MulEquiv.apply_symm_apply]
    exact hx

/-- A `Fintype` instance for semidirect products, needed for the kernel computations. -/
noncomputable instance instFintypeOrder16SemidirectProduct {N H : Type*} [Group N] [Group H]
    [Fintype N] [Fintype H] (φ : H →* MulAut N) :
    Fintype (SemidirectProduct N H φ) :=
  Fintype.ofEquiv (N × H) SemidirectProduct.equivProd.symm

/-- The invariant tuple `(|Z(G)|, #{x²=1}, #{x⁴=1}, #squares)` of a group. -/
private noncomputable def wildInvariantOf (H : Type*) [Group H] : ℕ × ℕ × ℕ × ℕ :=
  (Nat.card (Subgroup.center H), pow_eq_one_card H 2, pow_eq_one_card H 4, sq_image_card H)

private theorem wildInvariantOf_eq_of_mulEquiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) : wildInvariantOf H = wildInvariantOf K := by
  refine Prod.ext (card_center_eq_of_mulEquiv e) (Prod.ext (pow_eq_one_card_eq_of_mulEquiv 2 e)
    (Prod.ext (pow_eq_one_card_eq_of_mulEquiv 4 e) (sq_image_card_eq_of_mulEquiv e)))

/-- The invariant tuples of the 14 representatives. -/
private def order16_wild_invariant : Fin 14 → ℕ × ℕ × ℕ × ℕ
  | 0 => (16, 16, 16, 1)
  | 1 => (16, 4, 8, 4)
  | 2 => (2, 6, 12, 4)
  | 3 => (4, 4, 8, 4)
  | 4 => (2, 10, 12, 4)
  | 5 => (2, 2, 12, 4)
  | 6 => (16, 2, 4, 8)
  | 7 => (16, 8, 16, 2)
  | 8 => (4, 12, 16, 2)
  | 9 => (4, 8, 16, 3)
  | 10 => (4, 8, 16, 2)
  | 11 => (4, 4, 16, 2)
  | 12 => (4, 4, 16, 3)
  | 13 => (16, 4, 16, 4)

set_option linter.unusedFintypeInType false in
/-- Helper: establish the invariant tuple by four kernel computations. -/
private theorem wildInvariantOf_eq_of_counts {H : Type*} [Group H] [Fintype H]
    [Fintype (Subgroup.center H)] [Fintype {x : H // x ^ 2 = 1}]
    [Fintype {x : H // x ^ 4 = 1}] [Fintype {y : H // ∃ x : H, x ^ 2 = y}]
    {a b c d : ℕ}
    (h1 : Fintype.card (Subgroup.center H) = a)
    (h2 : Fintype.card {x : H // x ^ 2 = 1} = b)
    (h3 : Fintype.card {x : H // x ^ 4 = 1} = c)
    (h4 : Fintype.card {y : H // ∃ x : H, x ^ 2 = y} = d) :
    wildInvariantOf H = (a, b, c, d) :=
  Prod.ext (nat_card_eq_of_fintype_card_eq h1) (Prod.ext (nat_card_eq_of_fintype_card_eq h2)
    (Prod.ext (nat_card_eq_of_fintype_card_eq h3) (nat_card_eq_of_fintype_card_eq h4)))

private theorem invariant_G0 : wildInvariantOf order16_wild_G0 = (16, 16, 16, 1) := by
  obtain ⟨e⟩ := order16_A5_iso_concrete
  rw [wildInvariantOf_eq_of_mulEquiv e]
  exact wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G1 : wildInvariantOf order16_wild_G1 = (16, 4, 8, 4) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G2 : wildInvariantOf order16_wild_G2 = (2, 6, 12, 4) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G3 : wildInvariantOf order16_wild_G3 = (4, 4, 8, 4) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G4 : wildInvariantOf order16_wild_G4 = (2, 10, 12, 4) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G5 : wildInvariantOf order16_wild_G5 = (2, 2, 12, 4) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G6 : wildInvariantOf order16_wild_G6 = (16, 2, 4, 8) := by
  obtain ⟨e⟩ := order16_A1_iso_concrete
  rw [wildInvariantOf_eq_of_mulEquiv e]
  exact wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G7 : wildInvariantOf order16_wild_G7 = (16, 8, 16, 2) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G8 : wildInvariantOf order16_wild_G8 = (4, 12, 16, 2) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G9 : wildInvariantOf order16_wild_G9 = (4, 8, 16, 3) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G10 : wildInvariantOf order16_wild_G10 = (4, 8, 16, 2) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G11 : wildInvariantOf order16_wild_G11 = (4, 4, 16, 2) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G12 : wildInvariantOf order16_wild_G12 = (4, 4, 16, 3) :=
  wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem invariant_G13 : wildInvariantOf order16_wild_G13 = (16, 4, 16, 4) := by
  obtain ⟨e⟩ := order16_A3_iso_concrete
  rw [wildInvariantOf_eq_of_mulEquiv e]
  exact wildInvariantOf_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem order16_wild_invariant_spec (i : Fin 14) :
    wildInvariantOf (order16_wild_reps i) = order16_wild_invariant i := by
  fin_cases i
  · exact invariant_G0
  · exact invariant_G1
  · exact invariant_G2
  · exact invariant_G3
  · exact invariant_G4
  · exact invariant_G5
  · exact invariant_G6
  · exact invariant_G7
  · exact invariant_G8
  · exact invariant_G9
  · exact invariant_G10
  · exact invariant_G11
  · exact invariant_G12
  · exact invariant_G13

/-- Public projection of the order-`16` invariant table: the number of
elements whose fourth power is one. -/
def order16_wild_pow_four_card : Fin 14 → ℕ
  | 0 => 16 | 1 => 8 | 2 => 12 | 3 => 8 | 4 => 12 | 5 => 12 | 6 => 4
  | 7 => 16 | 8 => 16 | 9 => 16 | 10 => 16 | 11 => 16 | 12 => 16 | 13 => 16

/-- Public projection of the order-`16` invariant table: the number of
distinct squares. -/
def order16_wild_square_image_card : Fin 14 → ℕ
  | 0 => 1 | 1 => 4 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 4 | 6 => 8
  | 7 => 2 | 8 => 2 | 9 => 3 | 10 => 2 | 11 => 2 | 12 => 3 | 13 => 4

theorem pow_four_card_order16_wild_reps (i : Fin 14) :
    pow_eq_one_card (order16_wild_reps i) 4 =
      order16_wild_pow_four_card i := by
  have h := congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.1)
    (order16_wild_invariant_spec i)
  rw [show order16_wild_pow_four_card i =
      (order16_wild_invariant i).2.2.1 by fin_cases i <;> rfl]
  simpa [wildInvariantOf] using h

theorem square_image_card_order16_wild_reps (i : Fin 14) :
    sq_image_card (order16_wild_reps i) =
      order16_wild_square_image_card i := by
  have h := congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.2)
    (order16_wild_invariant_spec i)
  rw [show order16_wild_square_image_card i =
      (order16_wild_invariant i).2.2.2 by fin_cases i <;> rfl]
  simpa [wildInvariantOf] using h

end Invariants

/-! ### Recognition lemmas

For each case of Wild's extension analysis we build an explicit homomorphism from the
model group to `G`, prove it injective by kernel analysis, and conclude that it is an
isomorphism by cardinality.
-/

section Recognition

variable {G : Type*} [Group G]

/-- An injective hom between finite groups of equal cardinality is an isomorphism. -/
private noncomputable def mulEquivOfInjectiveCard {M : Type*} [Group M] [Finite M] [Finite G]
    (Φ : M →* G) (hi : Function.Injective Φ) (hcard : Nat.card M = Nat.card G) : M ≃* G := by
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype G := Fintype.ofFinite G
  exact MulEquiv.ofBijective Φ ((Fintype.bijective_iff_injective_and_card Φ).mpr
    ⟨hi, by rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]⟩)

/-- Evaluation of `zmodPowHom` at an arbitrary element. -/
private lemma zmodPowHom_eval {n : ℕ} [NeZero n] (g : G) (hg : g ^ n = 1)
    (m : Multiplicative (ZMod n)) :
    zmodPowHom n g hg m = g ^ (Multiplicative.toAdd m).val := by
  have hm : m = Multiplicative.ofAdd (((Multiplicative.toAdd m).val : ZMod n)) := by
    rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
  conv_lhs => rw [hm]
  exact zmodPowHom_apply n g hg _

/-- `zmodPowHom` at the generator. -/
private lemma zmodPowHom_gen {n : ℕ} (hn : 2 ≤ n) (g : G) (hg : g ^ n = 1) :
    zmodPowHom n g hg (Multiplicative.ofAdd (1 : ZMod n)) = g := by
  haveI : NeZero n := ⟨by omega⟩
  rw [zmodPowHom_eval, toAdd_ofAdd, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn, pow_one]

/-- `zmodPowHom` is injective when `g` has order exactly `n`. -/
private lemma zmodPowHom_injective {n : ℕ} (hn : 0 < n) (g : G) (hg : g ^ n = 1)
    (hord : orderOf g = n) : Function.Injective (zmodPowHom n g hg) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  refine (injective_iff_map_eq_one _).mpr ?_
  intro a ha
  rw [zmodPowHom_eval] at ha
  have hdvd : n ∣ (Multiplicative.toAdd a).val := by
    have hdvd0 : orderOf g ∣ (Multiplicative.toAdd a).val := orderOf_dvd_of_pow_eq_one ha
    rwa [hord] at hdvd0
  have hlt : (Multiplicative.toAdd a).val < n := ZMod.val_lt _
  have h0 : (Multiplicative.toAdd a).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  have h0' : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).mp h0
  rw [← ofAdd_toAdd a, h0', ofAdd_zero]

/-- Every element of `C8g` is a power of the generator. -/
private lemma c8g_decomp (p : C8g) : p = xC8 ^ (Multiplicative.toAdd p).val := by
  revert p; decide

/-- Homs out of `C8g` agree if they agree on the generator. -/
private lemma c8g_hom_ext {M : Type*} [Monoid M] {f g : C8g →* M}
    (h : f xC8 = g xC8) : f = g := by
  refine MonoidHom.ext fun p => ?_
  conv_lhs => rw [c8g_decomp p]
  conv_rhs => rw [c8g_decomp p]
  rw [map_pow, map_pow, h]

/-- Every element of `K8g` is `x^a * y^b`. -/
private lemma k8g_decomp (p : K8g) :
    p = xK8 ^ (Multiplicative.toAdd p.1).val * yK8 ^ (Multiplicative.toAdd p.2).val := by
  revert p; decide

/-- Homs out of `K8g` agree if they agree on the two generators. -/
private lemma k8g_hom_ext {M : Type*} [Monoid M] {f g : K8g →* M}
    (hx : f xK8 = g xK8) (hy : f yK8 = g yK8) : f = g := by
  refine MonoidHom.ext fun p => ?_
  conv_lhs => rw [k8g_decomp p]
  conv_rhs => rw [k8g_decomp p]
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hx, hy]

/-- Every element of `Multiplicative (ZMod 4)` is a power of `ofAdd 1`. -/
private lemma c4g_decomp (p : Multiplicative (ZMod 4)) :
    p = (Multiplicative.ofAdd (1 : ZMod 4)) ^ (Multiplicative.toAdd p).val := by
  revert p; decide

/-- Homs out of `Multiplicative (ZMod 4)` agree if they agree on the generator. -/
private lemma c4g_hom_ext {M : Type*} [Monoid M] {f g : Multiplicative (ZMod 4) →* M}
    (h : f (Multiplicative.ofAdd (1 : ZMod 4)) = g (Multiplicative.ofAdd (1 : ZMod 4))) :
    f = g := by
  refine MonoidHom.ext fun p => ?_
  conv_lhs => rw [c4g_decomp p]
  conv_rhs => rw [c4g_decomp p]
  rw [map_pow, map_pow, h]

/-- The hom `K8g →* G` sending the generators to commuting elements `x, w`. -/
private noncomputable def k8gHom (x w : G) (hx : x ^ 4 = 1) (hw : w ^ 2 = 1)
    (hcomm : Commute x w) : K8g →* G :=
  (zmodPowHom 4 x hx).noncommCoprod (zmodPowHom 2 w hw) (by
    intro a b
    rw [zmodPowHom_eval, zmodPowHom_eval]
    exact hcomm.pow_pow _ _)

private lemma k8gHom_eval (x w : G) (hx : x ^ 4 = 1) (hw : w ^ 2 = 1) (hcomm : Commute x w)
    (p : K8g) : k8gHom x w hx hw hcomm p =
      x ^ (Multiplicative.toAdd p.1).val * w ^ (Multiplicative.toAdd p.2).val := by
  rcases p with ⟨a, b⟩
  simp only [k8gHom, MonoidHom.noncommCoprod_apply]
  rw [zmodPowHom_eval, zmodPowHom_eval]

private lemma k8gHom_x (x w : G) (hx : x ^ 4 = 1) (hw : w ^ 2 = 1) (hcomm : Commute x w) :
    k8gHom x w hx hw hcomm xK8 = x := by
  rw [k8gHom_eval]
  have h1 : (Multiplicative.toAdd (xK8.1 : Multiplicative (ZMod 4))).val = 1 := by decide
  have h2 : (Multiplicative.toAdd (xK8.2 : Multiplicative (ZMod 2))).val = 0 := by decide
  rw [h1, h2, pow_one, pow_zero, mul_one]

private lemma k8gHom_y (x w : G) (hx : x ^ 4 = 1) (hw : w ^ 2 = 1) (hcomm : Commute x w) :
    k8gHom x w hx hw hcomm yK8 = w := by
  rw [k8gHom_eval]
  have h1 : (Multiplicative.toAdd (yK8.1 : Multiplicative (ZMod 4))).val = 0 := by decide
  have h2 : (Multiplicative.toAdd (yK8.2 : Multiplicative (ZMod 2))).val = 1 := by decide
  rw [h1, h2, pow_one, pow_zero, one_mul]

/-- The K8-hom is injective when `x` has order 4 and `w ∉ ⟨x⟩`. -/
private lemma k8gHom_injective (x w : G) (hx4 : orderOf x = 4)
    (hcomm : Commute x w) (hw_notin : w ∉ Subgroup.zpowers x)
    (hx : x ^ 4 = 1) (hw : w ^ 2 = 1) :
    Function.Injective (k8gHom x w hx hw hcomm) := by
  refine (injective_iff_map_eq_one _).mpr ?_
  rintro ⟨a, b⟩ hab
  rw [k8gHom_eval] at hab
  have hbv_lt : (Multiplicative.toAdd b).val < 2 := ZMod.val_lt _
  have hav_lt : (Multiplicative.toAdd a).val < 4 := ZMod.val_lt _
  have hbv0 : (Multiplicative.toAdd b).val = 0 := by
    by_contra hbv1
    have hbv1' : (Multiplicative.toAdd b).val = 1 := by omega
    rw [hbv1', pow_one] at hab
    refine hw_notin ?_
    have hw_eq : w = (x ^ (Multiplicative.toAdd a).val)⁻¹ :=
      eq_inv_of_mul_eq_one_right hab
    rw [hw_eq]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
  rw [hbv0, pow_zero, mul_one] at hab
  have hav0 : (Multiplicative.toAdd a).val = 0 := by
    have hdvd : orderOf x ∣ (Multiplicative.toAdd a).val := orderOf_dvd_of_pow_eq_one hab
    rw [hx4] at hdvd
    omega
  have ha1 : a = 1 := by
    have h0 : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).mp hav0
    rw [← ofAdd_toAdd a, h0, ofAdd_zero]
  have hb1 : b = 1 := by
    have h0 : Multiplicative.toAdd b = 0 := (ZMod.val_eq_zero _).mp hbv0
    rw [← ofAdd_toAdd b, h0, ofAdd_zero]
  rw [ha1, hb1]
  rfl

/-- Recognition of split extensions by `C₂`: if `f : N →* G` is injective, `t ∉ f.range`
has `t² = 1`, conjugation by `t` realizes `φ(gen)` on `f.range`, and `|G| = 2·|N|`,
then `G ≅ N ⋊[φ] C₂`. -/
private lemma recog_split_c2 {N : Type*} [Group N] [Finite N] [Finite G]
    (φ : Multiplicative (ZMod 2) →* MulAut N)
    (f : N →* G) (hf : Function.Injective f)
    (t : G) (ht2 : t ^ 2 = 1) (htr : t ∉ f.range)
    (hconj : ∀ n : N, t * f n * t⁻¹ = f (φ (Multiplicative.ofAdd 1) n))
    (hcard : Nat.card G = 2 * Nat.card N) :
    Nonempty (G ≃* SemidirectProduct N (Multiplicative (ZMod 2)) φ) := by
  classical
  haveI : Finite (SemidirectProduct N (Multiplicative (ZMod 2)) φ) :=
    Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hcompat : ∀ s : Multiplicative (ZMod 2),
      f.comp (φ s).toMonoidHom =
        (MulAut.conj (zmodPowHom 2 t ht2 s)).toMonoidHom.comp f := by
    intro s
    rcases c2_two_cases s with rfl | rfl
    · refine MonoidHom.ext fun n => ?_
      simp
    · refine MonoidHom.ext fun n => ?_
      change f ((φ (Multiplicative.ofAdd 1)) n) =
        MulAut.conj (zmodPowHom 2 t ht2 (Multiplicative.ofAdd 1)) (f n)
      rw [zmodPowHom_gen (by norm_num) t ht2, MulAut.conj_apply, ← hconj n]
  set Φ := SemidirectProduct.lift f (zmodPowHom 2 t ht2) hcompat with hΦ
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro ⟨n, s⟩ hns
    have hval : Φ ⟨n, s⟩ = f n * zmodPowHom 2 t ht2 s := rfl
    rw [hval] at hns
    rcases c2_two_cases s with rfl | rfl
    · rw [map_one, mul_one] at hns
      have hn : n = 1 := hf (by rw [hns, map_one])
      rw [hn]
      rfl
    · exfalso
      rw [zmodPowHom_gen (by norm_num) t ht2] at hns
      have ht_eq : t = (f n)⁻¹ := eq_inv_of_mul_eq_one_right hns
      exact htr ⟨n⁻¹, by rw [map_inv, ← ht_eq]⟩
  have hcards : Nat.card (SemidirectProduct N (Multiplicative (ZMod 2)) φ) = Nat.card G := by
    rw [SemidirectProduct.card, hcard]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rw [h2, mul_comm]
  exact ⟨(mulEquivOfInjectiveCard Φ hinj hcards).symm⟩

/-- `g^k` reduced mod the exponent. -/
private lemma pow_mod_of_pow_eq_one {g : G} {m : ℕ} (hg : g ^ m = 1) (k : ℕ) :
    g ^ (k % m) = g ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k m]
  rw [pow_add, pow_mul, hg, one_pow, one_mul]

private lemma pow_val_add' {g : G} {m : ℕ} [NeZero m] (hg : g ^ m = 1) (i j : ZMod m) :
    g ^ (i + j).val = g ^ i.val * g ^ j.val := by
  rw [ZMod.val_add, pow_mod_of_pow_eq_one hg, pow_add]

/-- The hom `QuaternionGroup n →* G` sending `a 1 ↦ g` and `xa 0 ↦ t`, given the
quaternion relations `g^(2n) = 1`, `t² = gⁿ`, `t g t⁻¹ = g⁻¹`. -/
private def quaternionHom (n : ℕ) [NeZero n] (g t : G)
    (hg : g ^ (2 * n) = 1) (ht2 : t ^ 2 = g ^ n) (hconj : t * g * t⁻¹ = g⁻¹) :
    QuaternionGroup n →* G where
  toFun q := match q with
    | .a i => g ^ i.val
    | .xa i => t * g ^ i.val
  map_one' := by
    change g ^ (0 : ZMod (2 * n)).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    have hB : t * g⁻¹ * t⁻¹ = g := by
      have h2 : (t * g * t⁻¹)⁻¹ = (g⁻¹)⁻¹ := by rw [hconj]
      simpa [mul_inv_rev, mul_assoc] using h2
    have hgt : g * t = t * g⁻¹ := by
      conv_lhs => rw [← hB]
      group
    have key : ∀ k : ℕ, g ^ k * t = t * (g ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => simp
      | succ m ih =>
        calc g ^ (m + 1) * t = g ^ m * (g * t) := by rw [pow_succ]; group
          _ = g ^ m * (t * g⁻¹) := by rw [hgt]
          _ = (g ^ m * t) * g⁻¹ := by group
          _ = t * (g ^ m)⁻¹ * g⁻¹ := by rw [ih]
          _ = t * (g ^ (m + 1))⁻¹ := by rw [pow_succ]; group
    have hsub : ∀ i j : ZMod (2 * n), g ^ (j - i).val = (g ^ i.val)⁻¹ * g ^ j.val := by
      intro i j
      have h1 : g ^ i.val * g ^ (j - i).val = g ^ j.val := by
        rw [← pow_val_add' hg, show i + (j - i) = j by ring]
      rw [← h1]
      group
    rintro (i | i) (j | j)
    · change g ^ (i + j).val = g ^ i.val * g ^ j.val
      exact pow_val_add' hg i j
    · change t * g ^ (j - i).val = g ^ i.val * (t * g ^ j.val)
      calc t * g ^ (j - i).val = (t * (g ^ i.val)⁻¹) * g ^ j.val := by rw [hsub i j]; group
        _ = (g ^ i.val * t) * g ^ j.val := by rw [key i.val]
        _ = g ^ i.val * (t * g ^ j.val) := by group
    · change t * g ^ (i + j).val = t * g ^ i.val * g ^ j.val
      rw [pow_val_add' hg, mul_assoc]
    · change g ^ ((n : ZMod (2 * n)) + j - i).val = t * g ^ i.val * (t * g ^ j.val)
      have hn_lt : n < 2 * n := by
        have := NeZero.pos n
        omega
      have hval_n : ((n : ZMod (2 * n))).val = n := ZMod.val_natCast_of_lt hn_lt
      have h1 : (n : ZMod (2 * n)) + j - i = (n : ZMod (2 * n)) + (j - i) := by ring
      rw [h1, pow_val_add' hg, hval_n, hsub i j]
      symm
      calc t * g ^ i.val * (t * g ^ j.val)
          = t * (g ^ i.val * t) * g ^ j.val := by group
        _ = t * (t * (g ^ i.val)⁻¹) * g ^ j.val := by rw [key i.val]
        _ = t ^ 2 * ((g ^ i.val)⁻¹ * g ^ j.val) := by rw [pow_two]; group
        _ = g ^ n * ((g ^ i.val)⁻¹ * g ^ j.val) := by rw [ht2]

/-- Recognition of `Q₁₆`. -/
private lemma recog_G5 [Finite G] (hcard : Nat.card G = 16) (x t : G)
    (hx8 : orderOf x = 8) (ht2 : t ^ 2 = x ^ 4) (hconj : t * x * t⁻¹ = x⁻¹)
    (htx : t ∉ Subgroup.zpowers x) :
    Nonempty (G ≃* order16_wild_G5) := by
  have hx16 : x ^ (2 * 4) = 1 := by
    rw [show 2 * 4 = 8 from rfl, ← hx8]
    exact pow_orderOf_eq_one x
  set ρ := quaternionHom 4 x t hx16 ht2 hconj with hρ
  have hinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro (i | i) h
    · have hval : ρ (QuaternionGroup.a i) = x ^ i.val := rfl
      rw [hval] at h
      have hdvd : (8 : ℕ) ∣ i.val := by
        have h0 : orderOf x ∣ i.val := orderOf_dvd_of_pow_eq_one h
        rwa [hx8] at h0
      have hlt : i.val < 8 := ZMod.val_lt i
      have h0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      rw [QuaternionGroup.one_def]
      congr 1
      exact (ZMod.val_eq_zero i).mp h0
    · exfalso
      have hval : ρ (QuaternionGroup.xa i) = t * x ^ i.val := rfl
      rw [hval] at h
      have ht_eq : t = (x ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
      exact htx (ht_eq ▸ Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
  have hcards : Nat.card (QuaternionGroup 4) = Nat.card G := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card, hcard]
  exact ⟨(mulEquivOfInjectiveCard ρ hinj hcards).symm⟩

/-- Recognition of the split `C₈ ⋊ C₂` extensions (`G₂`, `G₃`, `G₄`). -/
private lemma recog_c8_split [Finite G] (hcard : Nat.card G = 16)
    (φ : Multiplicative (ZMod 2) →* MulAut C8g) {k : ℕ}
    (hφ : φ (Multiplicative.ofAdd 1) xC8 = xC8 ^ k)
    (x t : G) (hx8 : orderOf x = 8) (ht2 : t ^ 2 = 1) (htx : t ∉ Subgroup.zpowers x)
    (hconj : t * x * t⁻¹ = x ^ k) :
    Nonempty (G ≃* SemidirectProduct C8g (Multiplicative (ZMod 2)) φ) := by
  have hx8' : x ^ 8 = 1 := by rw [← hx8]; exact pow_orderOf_eq_one x
  have hf : Function.Injective (zmodPowHom 8 x hx8') :=
    zmodPowHom_injective (by norm_num) x hx8' hx8
  have hfx : zmodPowHom 8 x hx8' xC8 = x := zmodPowHom_gen (by norm_num) x hx8'
  have hfr : t ∉ (zmodPowHom 8 x hx8').range := by
    rintro ⟨a, ha⟩
    apply htx
    rw [← ha, zmodPowHom_eval]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  have hhom : (MulAut.conj t).toMonoidHom.comp (zmodPowHom 8 x hx8') =
      (zmodPowHom 8 x hx8').comp (φ (Multiplicative.ofAdd 1)).toMonoidHom := by
    refine c8g_hom_ext ?_
    change MulAut.conj t (zmodPowHom 8 x hx8' xC8) =
      zmodPowHom 8 x hx8' (φ (Multiplicative.ofAdd 1) xC8)
    rw [hfx, hφ, MulAut.conj_apply, hconj, map_pow, hfx]
  have hpt : ∀ n : C8g, t * zmodPowHom 8 x hx8' n * t⁻¹ =
      zmodPowHom 8 x hx8' (φ (Multiplicative.ofAdd 1) n) := by
    intro n
    have h := DFunLike.congr_fun hhom n
    simpa [MulAut.conj_apply] using h
  exact recog_split_c2 φ (zmodPowHom 8 x hx8') hf t ht2 hfr hpt
    (by rw [hcard, card_C8g])

/-- Recognition of the split `K₈ ⋊ C₂` extensions (`G₈`, `G₉`, `G₁₀`).
The action values are supplied as elements `px py : K8g` together with the corresponding
conjugation relations in `G`, expressed via the canonical decomposition `xᵃwᵇ`. -/
private lemma recog_k8_split [Finite G] (hcard : Nat.card G = 16)
    (φ : Multiplicative (ZMod 2) →* MulAut K8g) {px py : K8g}
    (hφx : φ (Multiplicative.ofAdd 1) xK8 = px)
    (hφy : φ (Multiplicative.ofAdd 1) yK8 = py)
    (x w t : G) (hx4 : orderOf x = 4) (hw2 : w ^ 2 = 1) (hcomm : Commute x w)
    (hw_notin : w ∉ Subgroup.zpowers x)
    (Hs : Subgroup G) (hxH : x ∈ Hs) (hwH : w ∈ Hs) (htH : t ∉ Hs)
    (ht2 : t ^ 2 = 1)
    (hconjx : t * x * t⁻¹ =
      x ^ (Multiplicative.toAdd px.1).val * w ^ (Multiplicative.toAdd px.2).val)
    (hconjy : t * w * t⁻¹ =
      x ^ (Multiplicative.toAdd py.1).val * w ^ (Multiplicative.toAdd py.2).val) :
    Nonempty (G ≃* SemidirectProduct K8g (Multiplicative (ZMod 2)) φ) := by
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hf : Function.Injective (k8gHom x w hx4' hw2 hcomm) :=
    k8gHom_injective x w hx4 hcomm hw_notin hx4' hw2
  have hfr : t ∉ (k8gHom x w hx4' hw2 hcomm).range := by
    rintro ⟨p, hp⟩
    apply htH
    rw [← hp, k8gHom_eval]
    exact Hs.mul_mem (Hs.pow_mem hxH _) (Hs.pow_mem hwH _)
  have hhom : (MulAut.conj t).toMonoidHom.comp (k8gHom x w hx4' hw2 hcomm) =
      (k8gHom x w hx4' hw2 hcomm).comp (φ (Multiplicative.ofAdd 1)).toMonoidHom := by
    refine k8g_hom_ext ?_ ?_
    · change MulAut.conj t (k8gHom x w hx4' hw2 hcomm xK8) =
        k8gHom x w hx4' hw2 hcomm (φ (Multiplicative.ofAdd 1) xK8)
      rw [k8gHom_x, hφx, MulAut.conj_apply, hconjx, k8gHom_eval]
    · change MulAut.conj t (k8gHom x w hx4' hw2 hcomm yK8) =
        k8gHom x w hx4' hw2 hcomm (φ (Multiplicative.ofAdd 1) yK8)
      rw [k8gHom_y, hφy, MulAut.conj_apply, hconjy, k8gHom_eval]
  have hpt : ∀ n : K8g, t * k8gHom x w hx4' hw2 hcomm n * t⁻¹ =
      k8gHom x w hx4' hw2 hcomm (φ (Multiplicative.ofAdd 1) n) := by
    intro n
    have h := DFunLike.congr_fun hhom n
    simpa [MulAut.conj_apply] using h
  exact recog_split_c2 φ (k8gHom x w hx4' hw2 hcomm) hf t ht2 hfr hpt
    (by rw [hcard, card_K8g])

/-- Recognition of `Q₈ × C₂` (`G₁₁`), from a `(K₈, ψ₃, x²)`-extension. -/
private lemma recog_G11 [Finite G] (hcard : Nat.card G = 16) (x w t : G)
    (Hs : Subgroup G) (hxH : x ∈ Hs) (hwH : w ∈ Hs) (htH : t ∉ Hs)
    (hx4 : orderOf x = 4) (hw2 : w ^ 2 = 1)
    (hw_notin : w ∉ Subgroup.zpowers x) (hcommxw : Commute x w)
    (hconjx : t * x * t⁻¹ = x⁻¹) (hcommtw : Commute t w) (ht2 : t ^ 2 = x ^ 2) :
    Nonempty (G ≃* order16_wild_G11) := by
  have hx4' : x ^ (2 * 2) = 1 := by
    rw [show 2 * 2 = 4 from rfl, ← hx4]
    exact pow_orderOf_eq_one x
  set ρ := quaternionHom 2 x t hx4' ht2 hconjx with hρ
  have hρa : ∀ i : ZMod 4, ρ (QuaternionGroup.a i) = x ^ i.val := fun _ => rfl
  have hρxa : ∀ i : ZMod 4, ρ (QuaternionGroup.xa i) = t * x ^ i.val := fun _ => rfl
  have hcomm' : ∀ (q : QuaternionGroup 2) (c : Multiplicative (ZMod 2)),
      Commute (ρ q) (zmodPowHom 2 w hw2 c) := by
    intro q c
    have h1 : Commute (ρ q) w := by
      rcases q with i | i
      · rw [hρa]
        exact hcommxw.pow_left _
      · rw [hρxa]
        exact Commute.mul_left hcommtw (hcommxw.pow_left _)
    rw [zmodPowHom_eval]
    exact h1.pow_right _
  set Φ := ρ.noncommCoprod (zmodPowHom 2 w hw2) hcomm' with hΦ
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro ⟨q, c⟩ h
    have hval : Φ (q, c) = ρ q * zmodPowHom 2 w hw2 c := rfl
    rw [hval, zmodPowHom_eval] at h
    have hq1 : q = 1 := by
      rcases c2_two_cases c with rfl | rfl
      · -- c = 1 : ρ q = 1
        have h1 : ρ q = 1 := by simpa using h
        rcases q with i | i
        · rw [hρa] at h1
          have hdvd : (4 : ℕ) ∣ i.val := by
            have h0 : orderOf x ∣ i.val := orderOf_dvd_of_pow_eq_one h1
            rwa [hx4] at h0
          have h0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt i)
          rw [QuaternionGroup.one_def]
          congr 1
          exact (ZMod.val_eq_zero i).mp h0
        · exfalso
          rw [hρxa] at h1
          have ht_eq : t = (x ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
          exact htH (ht_eq ▸ Hs.inv_mem (Hs.pow_mem hxH _))
      · -- c = generator : ρ q * w = 1
        exfalso
        have hval1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 := by
          decide
        rw [hval1, pow_one] at h
        have hw_eq : w = (ρ q)⁻¹ := eq_inv_of_mul_eq_one_right h
        rcases q with i | i
        · rw [hρa] at hw_eq
          exact hw_notin (hw_eq ▸ Subgroup.inv_mem _
            (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
        · rw [hρxa] at hw_eq
          have ht_eq : t = w⁻¹ * (x ^ i.val)⁻¹ := by
            rw [hw_eq]
            group
          exact htH (ht_eq ▸ Hs.mul_mem (Hs.inv_mem hwH) (Hs.inv_mem (Hs.pow_mem hxH _)))
    have hc1 : c = 1 := by
      subst hq1
      rcases c2_two_cases c with rfl | rfl
      · rfl
      · exfalso
        have hval1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 := by
          decide
        rw [map_one, one_mul, hval1, pow_one] at h
        apply hw_notin
        rw [h]
        exact Subgroup.one_mem _
    rw [hq1, hc1]
    rfl
  have hcards : Nat.card (QuaternionGroup 2 × Multiplicative (ZMod 2)) = Nat.card G := by
    rw [hcard, Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
    simp
  exact ⟨(mulEquivOfInjectiveCard Φ hinj hcards).symm⟩

/-- Enumeration of `Multiplicative (ZMod 4)`. -/
private lemma c4_four_cases (h : Multiplicative (ZMod 4)) :
    h = 1 ∨ h = Multiplicative.ofAdd 1 ∨ h = Multiplicative.ofAdd 2 ∨
      h = Multiplicative.ofAdd 3 := by
  revert h; decide

/-- The `C₄ ⋊ C₄` model compatibility data, given `A, B` with `B A B⁻¹ = A⁻¹`. -/
private lemma c4_semidirect_compat (A B : G) (hA4 : A ^ 4 = 1) (hB4 : B ^ 4 = 1)
    (hconjBA : B * A * B⁻¹ = A⁻¹) :
    ∀ h : Multiplicative (ZMod 4),
      (zmodPowHom 4 A hA4).comp
          ((c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 h).toMonoidHom) =
        (MulAut.conj (zmodPowHom 4 B hB4 h)).toMonoidHom.comp (zmodPowHom 4 A hA4) := by
  have hA3 : A ^ (3 : ZMod 4).val = A⁻¹ := by
    have h3 : (3 : ZMod 4).val = 3 := by decide
    rw [h3]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact hA4
  have hA1 : A ^ (1 : ZMod 4).val = A := by
    have h1 : (1 : ZMod 4).val = 1 := by decide
    rw [h1, pow_one]
  have hc2 : B ^ 2 * A * (B ^ 2)⁻¹ = A := by
    calc B ^ 2 * A * (B ^ 2)⁻¹ = B * (B * A * B⁻¹) * B⁻¹ := by rw [pow_two]; group
      _ = B * A⁻¹ * B⁻¹ := by rw [hconjBA]
      _ = (B * A * B⁻¹)⁻¹ := by group
      _ = A⁻¹⁻¹ := by rw [hconjBA]
      _ = A := inv_inv A
  have hc3 : B ^ 3 * A * (B ^ 3)⁻¹ = A⁻¹ := by
    calc B ^ 3 * A * (B ^ 3)⁻¹ = B * (B ^ 2 * A * (B ^ 2)⁻¹) * B⁻¹ := by
          rw [pow_succ']
          group
      _ = B * A * B⁻¹ := by rw [hc2]
      _ = A⁻¹ := hconjBA
  have hB0 : zmodPowHom 4 B hB4 (1 : Multiplicative (ZMod 4)) = 1 := map_one _
  have hB1 : B ^ (1 : ZMod 4).val = B := by
    rw [show (1 : ZMod 4).val = 1 by decide, pow_one]
  have hB2 : B ^ (2 : ZMod 4).val = B ^ 2 := by
    rw [show (2 : ZMod 4).val = 2 by decide]
  have hB3 : B ^ (3 : ZMod 4).val = B ^ 3 := by
    rw [show (3 : ZMod 4).val = 3 by decide]
  intro h
  rcases c4_four_cases h with rfl | rfl | rfl | rfl
  all_goals refine c4g_hom_ext ?_
  all_goals simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rw [show (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 1)
        (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 4) by decide,
      hB0]
    simp
  · rw [show (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 (Multiplicative.ofAdd 1))
        (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (3 : ZMod 4) by decide]
    simp only [zmodPowHom_eval, toAdd_ofAdd]
    rw [hA3, hA1, hB1]
    exact hconjBA.symm
  · rw [show (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 (Multiplicative.ofAdd 2))
        (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (1 : ZMod 4) by decide]
    simp only [zmodPowHom_eval, toAdd_ofAdd]
    rw [hA1, hB2]
    exact hc2.symm
  · rw [show (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 (Multiplicative.ofAdd 3))
        (Multiplicative.ofAdd (1 : ZMod 4)) = Multiplicative.ofAdd (3 : ZMod 4) by decide]
    simp only [zmodPowHom_eval, toAdd_ofAdd]
    rw [hA3, hA1, hB3]
    exact hc3.symm

/-- Cardinality bridge for the `C₄ ⋊ C₄` model. -/
private lemma card_G12_model : Nat.card order16_wild_G12 = 16 := card_order16_wild_G12

/-- Recognition of `C₄ ⋊ C₄` (`G₁₂`) from ψ₃-shaped data: `t x t⁻¹ = x⁻¹`, `t² = w`
where `w` is a central involution outside `⟨x⟩`. -/
private lemma recog_G12_of_psi3 [Finite G] (hcard : Nat.card G = 16) (x w t : G)
    (Hs : Subgroup G) (hxH : x ∈ Hs) (hwH : w ∈ Hs) (htH : t ∉ Hs)
    (hx4 : orderOf x = 4) (hw2 : w ^ 2 = 1)
    (hw_notin : w ∉ Subgroup.zpowers x)
    (hconjx : t * x * t⁻¹ = x⁻¹) (ht2 : t ^ 2 = w) :
    Nonempty (G ≃* order16_wild_G12) := by
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have ht4 : t ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ht2]
    exact hw2
  have hcompat := c4_semidirect_compat x t hx4' ht4 hconjx
  set Φ := SemidirectProduct.lift (zmodPowHom 4 x hx4') (zmodPowHom 4 t ht4) hcompat with hΦ
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro ⟨n, s⟩ hns
    have hval : Φ ⟨n, s⟩ = zmodPowHom 4 x hx4' n * zmodPowHom 4 t ht4 s := rfl
    rw [hval, zmodPowHom_eval, zmodPowHom_eval] at hns
    set k := (Multiplicative.toAdd s).val with hk_def
    have hk4 : k < 4 := ZMod.val_lt _
    have hs0 : k = 0 := by
      interval_cases k
      · rfl
      · exfalso
        rw [pow_one] at hns
        have ht_eq : t = (x ^ (Multiplicative.toAdd n).val)⁻¹ :=
          eq_inv_of_mul_eq_one_right hns
        exact htH (ht_eq ▸ Hs.inv_mem (Hs.pow_mem hxH _))
      · exfalso
        rw [ht2] at hns
        have hw_eq : w = (x ^ (Multiplicative.toAdd n).val)⁻¹ :=
          eq_inv_of_mul_eq_one_right hns
        exact hw_notin (hw_eq ▸ Subgroup.inv_mem _
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
      · exfalso
        have ht3 : t ^ 3 = w * t := by
          rw [pow_succ, ht2]
        rw [ht3, ← mul_assoc] at hns
        have h2 : t = (x ^ (Multiplicative.toAdd n).val * w)⁻¹ :=
          eq_inv_of_mul_eq_one_right hns
        have ht_eq : t = w⁻¹ * (x ^ (Multiplicative.toAdd n).val)⁻¹ := by
          rw [h2, mul_inv_rev]
        exact htH (ht_eq ▸ Hs.mul_mem (Hs.inv_mem hwH) (Hs.inv_mem (Hs.pow_mem hxH _)))
    have hs1 : s = 1 := by
      have h0 : Multiplicative.toAdd s = 0 := (ZMod.val_eq_zero _).mp (hk_def ▸ hs0)
      rw [← ofAdd_toAdd s, h0, ofAdd_zero]
    rw [hs0, pow_zero, mul_one] at hns
    have hn0 : (Multiplicative.toAdd n).val = 0 := by
      have hdvd : orderOf x ∣ (Multiplicative.toAdd n).val := orderOf_dvd_of_pow_eq_one hns
      rw [hx4] at hdvd
      exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have hn1 : n = 1 := by
      have h0 : Multiplicative.toAdd n = 0 := (ZMod.val_eq_zero _).mp hn0
      rw [← ofAdd_toAdd n, h0, ofAdd_zero]
    rw [hs1, hn1]
    rfl
  have hcards : Nat.card order16_wild_G12 = Nat.card G := by
    rw [card_G12_model, hcard]
  exact ⟨(mulEquivOfInjectiveCard Φ hinj hcards).symm⟩

/-- Recognition of `C₄ ⋊ C₄` (`G₁₂`) from ψ₅-shaped data: `t x t⁻¹ = x w`,
`t w t⁻¹ = w`, `t² = x²`. -/
private lemma recog_G12_of_psi5 [Finite G] (hcard : Nat.card G = 16) (x w t : G)
    (Hs : Subgroup G) (hxH : x ∈ Hs) (hwH : w ∈ Hs) (htH : t ∉ Hs)
    (hx4 : orderOf x = 4) (hw2 : w ^ 2 = 1) (hcommxw : Commute x w)
    (hw_notin : w ∉ Subgroup.zpowers x)
    (hconjx : t * x * t⁻¹ = x * w) (hconjw : t * w * t⁻¹ = w) (ht2 : t ^ 2 = x ^ 2) :
    Nonempty (G ≃* order16_wild_G12) := by
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hx2_ne : x ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hx4] at hdvd
    omega
  have hwinv : w⁻¹ = w := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_two]
    exact hw2
  -- A := x * t
  have hA2 : (x * t) ^ 2 = w := by
    calc (x * t) ^ 2 = x * (t * x * t⁻¹) * t ^ 2 := by rw [pow_two, pow_two]; group
      _ = x * (x * w) * x ^ 2 := by rw [hconjx, ht2]
      _ = x ^ 2 * (w * x ^ 2) := by rw [pow_two]; group
      _ = x ^ 2 * (x ^ 2 * w) := by rw [(hcommxw.symm.pow_right 2).eq]
      _ = x ^ 4 * w := by group
      _ = w := by rw [hx4', one_mul]
  have hA4 : (x * t) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hA2]
    exact hw2
  have hAinv : (x * t)⁻¹ = x * w * t := by
    refine (inv_eq_of_mul_eq_one_right ?_)
    calc (x * t) * (x * w * t) = x * (t * x * t⁻¹) * ((t * w * t⁻¹) * t ^ 2) := by group
      _ = x * (x * w) * (w * x ^ 2) := by rw [hconjx, hconjw, ht2]
      _ = x ^ 2 * (w * w) * x ^ 2 := by rw [pow_two]; group
      _ = x ^ 2 * 1 * x ^ 2 := by
          rw [show w * w = 1 by rw [← pow_two]; exact hw2]
      _ = x ^ 4 := by group
      _ = 1 := hx4'
  have hcx' : t * x⁻¹ * t⁻¹ = (x * w)⁻¹ := by
    have h2 : (t * x * t⁻¹)⁻¹ = (x * w)⁻¹ := by rw [hconjx]
    simpa [mul_inv_rev, mul_assoc] using h2
  have hconjBA : x * (x * t) * x⁻¹ = (x * t)⁻¹ := by
    calc x * (x * t) * x⁻¹ = x ^ 2 * (t * x⁻¹ * t⁻¹) * t := by rw [pow_two]; group
      _ = x ^ 2 * (w⁻¹ * x⁻¹) * t := by rw [hcx', mul_inv_rev]
      _ = x ^ 2 * (w * x⁻¹) * t := by rw [hwinv]
      _ = x ^ 2 * (x⁻¹ * w) * t := by rw [(hcommxw.symm.inv_right).eq]
      _ = x * w * t := by group
      _ = (x * t)⁻¹ := hAinv.symm
  have hcompat := c4_semidirect_compat (x * t) x hA4 hx4' hconjBA
  set Φ := SemidirectProduct.lift (zmodPowHom 4 (x * t) hA4) (zmodPowHom 4 x hx4')
    hcompat with hΦ
  have hAnotH : x * t ∉ Hs := by
    intro h
    exact htH (by simpa using Hs.mul_mem (Hs.inv_mem hxH) h)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro ⟨n, s⟩ hns
    have hval : Φ ⟨n, s⟩ = zmodPowHom 4 (x * t) hA4 n * zmodPowHom 4 x hx4' s := rfl
    rw [hval, zmodPowHom_eval, zmodPowHom_eval] at hns
    set k := (Multiplicative.toAdd n).val with hk_def
    have hk4 : k < 4 := ZMod.val_lt _
    have hn0 : k = 0 := by
      interval_cases k
      · rfl
      · exfalso
        rw [pow_one] at hns
        have hA_eq : x * t = (x ^ (Multiplicative.toAdd s).val)⁻¹ :=
          eq_inv_of_mul_eq_one_left hns
        exact hAnotH (hA_eq ▸ Hs.inv_mem (Hs.pow_mem hxH _))
      · exfalso
        rw [hA2] at hns
        have hw_eq : w = (x ^ (Multiplicative.toAdd s).val)⁻¹ :=
          eq_inv_of_mul_eq_one_left hns
        exact hw_notin (hw_eq ▸ Subgroup.inv_mem _
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
      · exfalso
        have hA3 : (x * t) ^ 3 = w * (x * t) := by
          rw [pow_succ, hA2]
        rw [hA3, mul_assoc] at hns
        have h3 : (x * t) * x ^ (Multiplicative.toAdd s).val = w⁻¹ :=
          eq_inv_of_mul_eq_one_right hns
        have hA_eq : x * t = w⁻¹ * (x ^ (Multiplicative.toAdd s).val)⁻¹ := by
          rw [← h3]
          group
        exact hAnotH (hA_eq ▸ Hs.mul_mem (Hs.inv_mem hwH) (Hs.inv_mem (Hs.pow_mem hxH _)))
    have hn1 : n = 1 := by
      have h0 : Multiplicative.toAdd n = 0 := (ZMod.val_eq_zero _).mp (hk_def ▸ hn0)
      rw [← ofAdd_toAdd n, h0, ofAdd_zero]
    rw [hn0, pow_zero, one_mul] at hns
    have hs0 : (Multiplicative.toAdd s).val = 0 := by
      have hdvd : orderOf x ∣ (Multiplicative.toAdd s).val := orderOf_dvd_of_pow_eq_one hns
      rw [hx4] at hdvd
      exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have hs1 : s = 1 := by
      have h0 : Multiplicative.toAdd s = 0 := (ZMod.val_eq_zero _).mp hs0
      rw [← ofAdd_toAdd s, h0, ofAdd_zero]
    rw [hn1, hs1]
    rfl
  have hcards : Nat.card order16_wild_G12 = Nat.card G := by
    rw [card_G12_model, hcard]
  exact ⟨(mulEquivOfInjectiveCard Φ hinj hcards).symm⟩

/-- Coset decomposition along an index-2 subgroup. -/
private lemma decomp_index_two [Finite G] {H : Subgroup G} [H.Normal] (hidx : H.index = 2)
    {t : G} (ht : t ∉ H) (a : G) : a ∈ H ∨ ∃ h ∈ H, a = h * t := by
  by_cases haH : a ∈ H
  · exact Or.inl haH
  right
  haveI : Finite (G ⧸ H) := Quotient.finite _
  have hcardQ : Nat.card (G ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hqa : (a : G ⧸ H) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  have hqt : (t : G ⧸ H) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  have hordq : orderOf (a : G ⧸ H) = 2 := by
    have hdvd : orderOf (a : G ⧸ H) ∣ 2 := by
      rw [← hcardQ]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hqa
    · exact h2
  have hzp : Subgroup.zpowers (a : G ⧸ H) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hordq, hcardQ]
  have hmem : (t : G ⧸ H) ∈ Subgroup.zpowers (a : G ⧸ H) := by
    rw [hzp]
    exact Subgroup.mem_top _
  obtain ⟨m', hm'_lt, hm'⟩ :=
    exists_pow_eq_of_mem_zpowers (by rw [hordq]; norm_num) hmem
  rw [hordq] at hm'_lt
  interval_cases m'
  · have ht_one : (t : G ⧸ H) = 1 := by
      simpa [pow_zero] using hm'.symm
    exact False.elim (hqt ht_one)
  · have heq : (t : G ⧸ H) = (a : G ⧸ H) := by rw [← hm', pow_one]
    have hmem2 : t⁻¹ * a ∈ H := (QuotientGroup.eq).mp heq
    refine ⟨t * (t⁻¹ * a) * t⁻¹, ‹H.Normal›.conj_mem _ hmem2 t, ?_⟩
    group

end Recognition

/-! ### Exhaustiveness: the `C₈`-extension branch -/

section ClassifyC8

variable {G : Type*} [Group G]

/-- A nonabelian group of order 16 containing an element of order 8 is
semidihedral, modular, dihedral, or generalized quaternion. -/
theorem classify_of_order8_refined [Finite G] (hcard : Nat.card G = 16)
    (hnab : ¬ ∀ a b : G, a * b = b * a) (x : G) (hx8 : orderOf x = 8) :
    ∃ i : Fin 14, (i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) ∧
      Nonempty (G ≃* order16_wild_reps i) := by
  classical
  have hx8' : x ^ 8 = 1 := by rw [← hx8]; exact pow_orderOf_eq_one x
  have hHcard : Nat.card (Subgroup.zpowers x) = 8 := by rw [Nat.card_zpowers, hx8]
  have hHidx : (Subgroup.zpowers x).index = 2 := by
    have hmul := (Subgroup.zpowers x).card_mul_index
    rw [hHcard, hcard] at hmul
    omega
  haveI hHnorm : (Subgroup.zpowers x).Normal := normal_of_index_eq_two hHidx
  obtain ⟨t, ht⟩ : ∃ t : G, t ∉ Subgroup.zpowers x := by
    by_contra hc
    push Not at hc
    have htop : Subgroup.zpowers x = ⊤ := by
      rw [Subgroup.eq_top_iff']
      exact hc
    rw [htop, Subgroup.card_top, hcard] at hHcard
    omega
  have hconj_mem : t * x * t⁻¹ ∈ Subgroup.zpowers x :=
    hHnorm.conj_mem x (Subgroup.mem_zpowers x) t
  obtain ⟨m, hm_lt, hm⟩ :=
    exists_pow_eq_of_mem_zpowers (by rw [hx8]; norm_num) hconj_mem
  rw [hx8] at hm_lt
  -- conjugation formula on powers
  have hconjpow : ∀ j : ℕ, t * x ^ j * t⁻¹ = x ^ (m * j) := by
    intro j
    calc t * x ^ j * t⁻¹ = (t * x * t⁻¹) ^ j := by rw [← conj_pow]
      _ = (x ^ m) ^ j := by rw [← hm]
      _ = x ^ (m * j) := by rw [← pow_mul]
  -- the exponent m is a unit mod 8
  have hm_ord : orderOf (x ^ m) = 8 := by
    rw [hm]
    have h1 : t * x * t⁻¹ = (MulAut.conj t).toMonoidHom x := by
      simp [MulAut.conj_apply]
    rw [h1, orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective, hx8]
  have hm_unit : Nat.gcd 8 m = 1 := by
    rw [orderOf_pow x, hx8] at hm_ord
    have hmem : Nat.gcd 8 m ∈ Nat.divisors 8 :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 8 m, by norm_num⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;> rw [h] at hm_ord <;> omega
  -- v = t² lies in ⟨x⟩
  have ht2H : t ^ 2 ∈ Subgroup.zpowers x := by
    haveI : Finite (G ⧸ Subgroup.zpowers x) := Quotient.finite _
    rw [← QuotientGroup.eq_one_iff]
    have hq2 : ((t ^ 2 : G) : G ⧸ Subgroup.zpowers x) = ((t : G ⧸ Subgroup.zpowers x)) ^ 2 := by
      rfl
    rw [hq2]
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    have hcardQ : Nat.card (G ⧸ Subgroup.zpowers x) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hHidx
    rw [← hcardQ]
    exact orderOf_dvd_natCard _
  obtain ⟨k, hk_lt, hk⟩ :=
    exists_pow_eq_of_mem_zpowers (by rw [hx8]; norm_num) ht2H
  rw [hx8] at hk_lt
  -- hk : x ^ k = t ^ 2; the fixed-point constraint on k
  have hfix : x ^ (m * k) = x ^ k := by
    calc x ^ (m * k) = t * x ^ k * t⁻¹ := (hconjpow k).symm
      _ = t * t ^ 2 * t⁻¹ := by rw [hk]
      _ = t ^ 2 := by group
      _ = x ^ k := hk.symm
  have hdvd_mk : ∀ c : ℕ, m * k = k + c → x ^ c = 1 := by
    intro c hc
    have h1 : x ^ k * x ^ c = x ^ k * 1 := by
      rw [mul_one, ← pow_add, ← hc]
      exact hfix
    exact mul_left_cancel h1
  -- case analysis on m ∈ {1, 3, 5, 7}
  interval_cases m
  · -- m = 0 : not a unit
    exact absurd hm_unit (by decide)
  · -- m = 1 : t centralizes ⟨x⟩, so G is abelian — contradiction
    exfalso
    apply hnab
    have hCt : Commute x t := by
      have h1 : t * x * t⁻¹ = x := by rw [← hm, pow_one]
      have h2 : t * x = x * t := by
        calc t * x = (t * x * t⁻¹) * t := by group
          _ = x * t := by rw [h1]
      exact h2.symm
    have hgen : ∀ c : G, ∃ (i : ℤ) (e : ℕ), c = x ^ i * t ^ e := by
      intro c
      rcases decomp_index_two hHidx ht c with hc | ⟨h, hh, rfl⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
        exact ⟨i, 0, by rw [pow_zero, mul_one, hi]⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact ⟨i, 1, by rw [pow_one, hi]⟩
    intro a b
    obtain ⟨i, e, rfl⟩ := hgen a
    obtain ⟨j, f, rfl⟩ := hgen b
    have h1 : Commute (x ^ i) (x ^ j) := (Commute.refl x).zpow_zpow i j
    have h2 : Commute (x ^ i) (t ^ f) := (hCt.zpow_left i).pow_right f
    have h3 : Commute (t ^ e) (x ^ j) := (hCt.symm.pow_left e).zpow_right j
    have h4 : Commute (t ^ e) (t ^ f) := (Commute.refl t).pow_pow e f
    exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
  · exact absurd hm_unit (by decide)
  · -- m = 3 : semidihedral SD₁₆ = G₂
    -- constraint: x^(2k) = 1, so k ∈ {0, 4}
    have h2k : x ^ (2 * k) = 1 := hdvd_mk (2 * k) (by ring)
    have h8dvd : 8 ∣ 2 * k := by
      have := orderOf_dvd_of_pow_eq_one h2k
      rwa [hx8] at this
    have hk04 : k = 0 ∨ k = 4 := by omega
    have hφ : c2Action_phi2 (Multiplicative.ofAdd 1) xC8 = xC8 ^ 3 := by decide
    rcases hk04 with rfl | rfl
    · -- split
      have ht2 : t ^ 2 = 1 := by rw [← hk, pow_zero]
      exact ⟨2, by decide, recog_c8_split hcard c2Action_phi2 hφ x t hx8 ht2 ht (by rw [← hm])⟩
    · -- replace t by x·t
      have ht'2 : (x * t) ^ 2 = 1 := by
        calc (x * t) ^ 2 = x * (t * x * t⁻¹) * t ^ 2 := by rw [pow_two, pow_two]; group
          _ = x * x ^ 3 * x ^ 4 := by rw [← hm, ← hk]
          _ = x ^ 8 := by group
          _ = 1 := hx8'
      have ht' : x * t ∉ Subgroup.zpowers x := by
        intro hmem
        apply ht
        have h1 : t = x⁻¹ * (x * t) := by group
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) hmem
      have hconj' : (x * t) * x * (x * t)⁻¹ = x ^ 3 := by
        calc (x * t) * x * (x * t)⁻¹ = x * (t * x * t⁻¹) * x⁻¹ := by group
          _ = x * x ^ 3 * x⁻¹ := by rw [← hm]
          _ = x ^ 3 := by group
      exact ⟨2, by decide, recog_c8_split hcard c2Action_phi2 hφ x (x * t) hx8 ht'2 ht' hconj'⟩
  · exact absurd hm_unit (by decide)
  · -- m = 5 : modular group G₃
    have h4k : x ^ (4 * k) = 1 := hdvd_mk (4 * k) (by ring)
    have h8dvd : 8 ∣ 4 * k := by
      have := orderOf_dvd_of_pow_eq_one h4k
      rwa [hx8] at this
    have hkeven : k % 2 = 0 := by omega
    have hφ : c2Action_phi3 (Multiplicative.ofAdd 1) xC8 = xC8 ^ 5 := by decide
    -- replace t by x^(k/2) * t, whose square is trivial
    have hj : 6 * (k / 2) + k = 4 * k ∨ 6 * (k / 2) + k = 4 * k - 8 + 8 := by omega
    have ht'2 : (x ^ (k / 2) * t) ^ 2 = 1 := by
      have hstep : (x ^ (k / 2) * t) ^ 2 = x ^ (6 * (k / 2) + k) := by
        calc (x ^ (k / 2) * t) ^ 2
            = x ^ (k / 2) * (t * x ^ (k / 2) * t⁻¹) * t ^ 2 := by
              rw [pow_two, pow_two]; group
          _ = x ^ (k / 2) * x ^ (5 * (k / 2)) * x ^ k := by rw [hconjpow, ← hk]
          _ = x ^ (k / 2 + 5 * (k / 2) + k) := by rw [← pow_add, ← pow_add]
          _ = x ^ (6 * (k / 2) + k) := by ring_nf
      rw [hstep]
      -- 6*(k/2) + k = 4k mod 8, and 8 ∣ 4k
      obtain ⟨c, hc⟩ := h8dvd
      have h6k : 6 * (k / 2) + k = 8 * c := by omega
      rw [h6k, pow_mul, hx8', one_pow]
    have ht' : x ^ (k / 2) * t ∉ Subgroup.zpowers x := by
      intro hmem
      apply ht
      have h1 : t = (x ^ (k / 2))⁻¹ * (x ^ (k / 2) * t) := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _
      (Subgroup.mem_zpowers x) _)) hmem
    have hconj' : (x ^ (k / 2) * t) * x * (x ^ (k / 2) * t)⁻¹ = x ^ 5 := by
      calc (x ^ (k / 2) * t) * x * (x ^ (k / 2) * t)⁻¹
          = x ^ (k / 2) * (t * x * t⁻¹) * (x ^ (k / 2))⁻¹ := by group
        _ = x ^ (k / 2) * x ^ 5 * (x ^ (k / 2))⁻¹ := by rw [← hm]
        _ = x ^ 5 := by
            have hcomm : Commute (x ^ (k / 2)) (x ^ 5) := (Commute.refl x).pow_pow _ _
            rw [hcomm.eq]
            group
    exact ⟨3, by decide, recog_c8_split hcard c2Action_phi3 hφ x (x ^ (k / 2) * t) hx8 ht'2 ht' hconj'⟩
  · exact absurd hm_unit (by decide)
  · -- m = 7 : dihedral D₁₆ = G₄ or quaternion Q₁₆ = G₅
    have h6k : x ^ (6 * k) = 1 := hdvd_mk (6 * k) (by ring)
    have h8dvd : 8 ∣ 6 * k := by
      have := orderOf_dvd_of_pow_eq_one h6k
      rwa [hx8] at this
    have hk04 : k = 0 ∨ k = 4 := by omega
    have hxinv : x ^ 7 = x⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact hx8'
    rcases hk04 with rfl | rfl
    · -- split: D₁₆
      have ht2 : t ^ 2 = 1 := by rw [← hk, pow_zero]
      have hφ : c2Action_phi4 (Multiplicative.ofAdd 1) xC8 = xC8 ^ 7 := by decide
      exact ⟨4, by decide, recog_c8_split hcard c2Action_phi4 hφ x t hx8 ht2 ht (by rw [← hm])⟩
    · -- non-split: Q₁₆
      have ht2 : t ^ 2 = x ^ 4 := hk.symm
      have hconj' : t * x * t⁻¹ = x⁻¹ := by rw [← hm, hxinv]
      exact ⟨5, by decide, recog_G5 hcard x t hx8 ht2 hconj' ht⟩

private lemma classify_of_order8 [Finite G] (hcard : Nat.card G = 16)
    (hnab : ¬ ∀ a b : G, a * b = b * a) (x : G) (hx8 : orderOf x = 8) :
    ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
  obtain ⟨i, _, hi⟩ := classify_of_order8_refined hcard hnab x hx8
  exact ⟨i, hi⟩

end ClassifyC8

/-! ### Exhaustiveness: the `K₈`-extension branch -/

section ClassifyK8

variable {G : Type*} [Group G]

/-- ψ₃-shaped conjugation data (`t x t⁻¹ = x⁻¹`, `t w t⁻¹ = w`) yields `G₈`, `G₁₁` or `G₁₂`,
according to the value of `t²`. -/
private lemma classify_k8_psi3 [Finite G] (hcard : Nat.card G = 16)
    (x w t : G) (Hs : Subgroup G) (hxH : x ∈ Hs) (hwH : w ∈ Hs) (htH : t ∉ Hs)
    (hx4 : orderOf x = 4) (hw2 : w ^ 2 = 1)
    (hcomm : Commute x w) (hw_notin : w ∉ Subgroup.zpowers x)
    (hconjx : t * x * t⁻¹ = x⁻¹) (hconjw : t * w * t⁻¹ = w)
    (ht2v : t ^ 2 = 1 ∨ t ^ 2 = x ^ 2 ∨ t ^ 2 = w ∨ t ^ 2 = x ^ 2 * w) :
    ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hxx3 : x * x ^ 3 = 1 := by
    have h1 : x * x ^ 3 = x ^ 4 := by group
    rw [h1, hx4']
  have hxinv : x⁻¹ = x ^ 3 := inv_eq_of_mul_eq_one_right hxx3
  rcases ht2v with ht2 | ht2 | ht2 | ht2
  · -- t² = 1 : split extension, G₈ = K₈ ⋊_ψ₃ C₂
    refine ⟨8, ?_⟩
    have hφx : c2Action_psi3 (Multiplicative.ofAdd 1) xK8 =
        (Multiplicative.ofAdd (3 : ZMod 4), (1 : Multiplicative (ZMod 2))) := by decide
    have hφy : c2Action_psi3 (Multiplicative.ofAdd 1) yK8 =
        ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 2)) := by decide
    refine recog_k8_split hcard c2Action_psi3 hφx hφy x w t hx4 hw2 hcomm hw_notin
      Hs hxH hwH htH ht2 ?_ ?_
    · have h1 : (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4),
          (1 : Multiplicative (ZMod 2))).1).val = 3 := by decide
      have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4),
          (1 : Multiplicative (ZMod 2))).2).val = 0 := by decide
      rw [h1, h2, pow_zero, mul_one, hconjx, hxinv]
    · have h1 : (Multiplicative.toAdd ((1 : Multiplicative (ZMod 4)),
          Multiplicative.ofAdd (1 : ZMod 2)).1).val = 0 := by decide
      have h2 : (Multiplicative.toAdd ((1 : Multiplicative (ZMod 4)),
          Multiplicative.ofAdd (1 : ZMod 2)).2).val = 1 := by decide
      rw [h1, h2, pow_zero, one_mul, pow_one, hconjw]
  · -- t² = x² : G₁₁ = Q₈ × C₂
    have hcommtw : Commute t w := by
      have h1 : t * w = w * t := by
        calc t * w = t * w * t⁻¹ * t := by group
          _ = w * t := by rw [hconjw]
      exact h1
    exact ⟨11, recog_G11 hcard x w t Hs hxH hwH htH hx4 hw2 hw_notin hcomm hconjx
      hcommtw ht2⟩
  · -- t² = w : G₁₂
    exact ⟨12, recog_G12_of_psi3 hcard x w t Hs hxH hwH htH hx4 hw2 hw_notin hconjx ht2⟩
  · -- t² = x²w : rebase the central involution to x²w and recognize G₁₂ again
    have hw'H : x ^ 2 * w ∈ Hs := Hs.mul_mem (Hs.pow_mem hxH 2) hwH
    have hw'2 : (x ^ 2 * w) ^ 2 = 1 := by
      rw [(hcomm.pow_left 2).mul_pow, hw2, mul_one]
      have h1 : ((x ^ 2) ^ 2 : G) = x ^ 4 := by group
      rw [h1, hx4']
    have hw'_notin : x ^ 2 * w ∉ Subgroup.zpowers x := by
      intro hmem
      apply hw_notin
      have h1 : w = (x ^ 2)⁻¹ * (x ^ 2 * w) := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)) hmem
    exact ⟨12, recog_G12_of_psi3 hcard x (x ^ 2 * w) t Hs hxH hw'H htH hx4 hw'2
      hw'_notin hconjx ht2⟩

/-- ψ₅-shaped conjugation data (`t x t⁻¹ = x w`, `t w t⁻¹ = w`) yields `G₉` or `G₁₂`. -/
private lemma classify_k8_psi5 [Finite G] (hcard : Nat.card G = 16)
    (x w t : G) (Hs : Subgroup G) (hxH : x ∈ Hs) (hwH : w ∈ Hs) (htH : t ∉ Hs)
    (hx4 : orderOf x = 4) (hw2 : w ^ 2 = 1)
    (hcomm : Commute x w) (hw_notin : w ∉ Subgroup.zpowers x)
    (hconjx : t * x * t⁻¹ = x * w) (hconjw : t * w * t⁻¹ = w)
    (ht2v : t ^ 2 = 1 ∨ t ^ 2 = x ^ 2 ∨ t ^ 2 = w ∨ t ^ 2 = x ^ 2 * w) :
    ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hww : w * w = 1 := by rw [← pow_two]; exact hw2
  -- helper: any complement element with the same conjugation data and trivial square
  -- yields the split extension G₉
  have hsplit : ∀ s : G, s ∉ Hs → s * x * s⁻¹ = x * w → s * w * s⁻¹ = w → s ^ 2 = 1 →
      ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
    intro s hsH hcx hcw hs2
    refine ⟨9, ?_⟩
    have hφx : c2Action_psi5 (Multiplicative.ofAdd 1) xK8 =
        (Multiplicative.ofAdd (1 : ZMod 4), Multiplicative.ofAdd (1 : ZMod 2)) := by decide
    have hφy : c2Action_psi5 (Multiplicative.ofAdd 1) yK8 =
        ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 2)) := by decide
    refine recog_k8_split hcard c2Action_psi5 hφx hφy x w s hx4 hw2 hcomm hw_notin
      Hs hxH hwH hsH hs2 ?_ ?_
    · have h1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4),
          Multiplicative.ofAdd (1 : ZMod 2)).1).val = 1 := by decide
      have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4),
          Multiplicative.ofAdd (1 : ZMod 2)).2).val = 1 := by decide
      rw [h1, h2, pow_one, pow_one, hcx]
    · have h1 : (Multiplicative.toAdd ((1 : Multiplicative (ZMod 4)),
          Multiplicative.ofAdd (1 : ZMod 2)).1).val = 0 := by decide
      have h2 : (Multiplicative.toAdd ((1 : Multiplicative (ZMod 4)),
          Multiplicative.ofAdd (1 : ZMod 2)).2).val = 1 := by decide
      rw [h1, h2, pow_zero, one_mul, pow_one, hcw]
  -- the conjugation data is unchanged when t is replaced by x * t
  have htH' : x * t ∉ Hs := fun h => htH (by simpa using Hs.mul_mem (Hs.inv_mem hxH) h)
  have hconjx' : (x * t) * x * (x * t)⁻¹ = x * w := by
    calc (x * t) * x * (x * t)⁻¹ = x * (t * x * t⁻¹) * x⁻¹ := by group
      _ = x * (x * w) * x⁻¹ := by rw [hconjx]
      _ = x * x * (w * x⁻¹) := by group
      _ = x * x * (x⁻¹ * w) := by rw [hcomm.inv_left.eq]
      _ = x * w := by group
  have hconjw' : (x * t) * w * (x * t)⁻¹ = w := by
    calc (x * t) * w * (x * t)⁻¹ = x * (t * w * t⁻¹) * x⁻¹ := by group
      _ = x * w * x⁻¹ := by rw [hconjw]
      _ = w * x * x⁻¹ := by rw [hcomm.eq]
      _ = w := by group
  rcases ht2v with ht2 | ht2 | ht2 | ht2
  · exact hsplit t htH hconjx hconjw ht2
  · exact ⟨12, recog_G12_of_psi5 hcard x w t Hs hxH hwH htH hx4 hw2 hcomm hw_notin
      hconjx hconjw ht2⟩
  · -- t² = w : x * t squares to x², giving G₁₂
    have ht2' : (x * t) ^ 2 = x ^ 2 := by
      calc (x * t) ^ 2 = x * (t * x * t⁻¹) * t ^ 2 := by rw [pow_two, pow_two]; group
        _ = x * (x * w) * w := by rw [hconjx, ht2]
        _ = x * x * (w * w) := by group
        _ = x ^ 2 := by rw [hww, mul_one, ← pow_two]
    exact ⟨12, recog_G12_of_psi5 hcard x w (x * t) Hs hxH hwH htH' hx4 hw2 hcomm hw_notin
      hconjx' hconjw' ht2'⟩
  · -- t² = x²w : x * t squares to 1, giving G₉
    have ht2' : (x * t) ^ 2 = 1 := by
      calc (x * t) ^ 2 = x * (t * x * t⁻¹) * t ^ 2 := by rw [pow_two, pow_two]; group
        _ = x * (x * w) * (x ^ 2 * w) := by rw [hconjx, ht2]
        _ = x * x * (w * x ^ 2) * w := by group
        _ = x * x * (x ^ 2 * w) * w := by rw [(hcomm.symm.pow_right 2).eq]
        _ = x * x * x ^ 2 * (w * w) := by group
        _ = x * x * x ^ 2 * 1 := by rw [hww]
        _ = x ^ 4 := by group
        _ = 1 := hx4'
    exact hsplit (x * t) htH' hconjx' hconjw' ht2'

/-- ψ₆-shaped conjugation data (`t x t⁻¹ = x⁻¹`, `t w t⁻¹ = x² w`) yields `G₁₀`. -/
private lemma classify_k8_psi6 [Finite G] (hcard : Nat.card G = 16)
    (x w t : G) (Hs : Subgroup G) (hxH : x ∈ Hs) (hwH : w ∈ Hs) (htH : t ∉ Hs)
    (hx4 : orderOf x = 4) (hw2 : w ^ 2 = 1)
    (hcomm : Commute x w) (hw_notin : w ∉ Subgroup.zpowers x)
    (hconjx : t * x * t⁻¹ = x⁻¹) (hconjw : t * w * t⁻¹ = x ^ 2 * w)
    (ht2v : t ^ 2 = 1 ∨ t ^ 2 = x ^ 2 ∨ t ^ 2 = w ∨ t ^ 2 = x ^ 2 * w) :
    ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hww : w * w = 1 := by rw [← pow_two]; exact hw2
  have hxx3 : x * x ^ 3 = 1 := by
    have h1 : x * x ^ 3 = x ^ 4 := by group
    rw [h1, hx4']
  have hxinv : x⁻¹ = x ^ 3 := inv_eq_of_mul_eq_one_right hxx3
  have hx2inv : (x ^ 2)⁻¹ = x ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    have h1 : x ^ 2 * x ^ 2 = x ^ 4 := by group
    rw [h1, hx4']
  have hx2ne : x ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hx4] at hdvd
    omega
  -- helper: any complement element with this conjugation data and trivial square gives G₁₀
  have hsplit : ∀ s : G, s ∉ Hs → s * x * s⁻¹ = x⁻¹ → s * w * s⁻¹ = x ^ 2 * w →
      s ^ 2 = 1 → ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
    intro s hsH hcx hcw hs2
    refine ⟨10, ?_⟩
    have hφx : c2Action_psi6 (Multiplicative.ofAdd 1) xK8 =
        (Multiplicative.ofAdd (3 : ZMod 4), (1 : Multiplicative (ZMod 2))) := by decide
    have hφy : c2Action_psi6 (Multiplicative.ofAdd 1) yK8 =
        (Multiplicative.ofAdd (2 : ZMod 4), Multiplicative.ofAdd (1 : ZMod 2)) := by decide
    refine recog_k8_split hcard c2Action_psi6 hφx hφy x w s hx4 hw2 hcomm hw_notin
      Hs hxH hwH hsH hs2 ?_ ?_
    · have h1 : (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4),
          (1 : Multiplicative (ZMod 2))).1).val = 3 := by decide
      have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd (3 : ZMod 4),
          (1 : Multiplicative (ZMod 2))).2).val = 0 := by decide
      rw [h1, h2, pow_zero, mul_one, hcx, hxinv]
    · have h1 : (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4),
          Multiplicative.ofAdd (1 : ZMod 2)).1).val = 2 := by decide
      have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4),
          Multiplicative.ofAdd (1 : ZMod 2)).2).val = 1 := by decide
      rw [h1, h2, pow_one, hcw]
  rcases ht2v with ht2 | ht2 | ht2 | ht2
  · exact hsplit t htH hconjx hconjw ht2
  · -- t² = x² : replace t by x w t, which squares to 1
    have hsH' : x * w * t ∉ Hs := by
      intro h
      apply htH
      have h1 : t = (x * w)⁻¹ * (x * w * t) := by group
      rw [h1]
      exact Hs.mul_mem (Hs.inv_mem (Hs.mul_mem hxH hwH)) h
    have hcx' : (x * w * t) * x * (x * w * t)⁻¹ = x⁻¹ := by
      calc (x * w * t) * x * (x * w * t)⁻¹ = x * w * (t * x * t⁻¹) * w⁻¹ * x⁻¹ := by group
        _ = x * w * x⁻¹ * w⁻¹ * x⁻¹ := by rw [hconjx]
        _ = x * (w * x⁻¹) * w⁻¹ * x⁻¹ := by group
        _ = x * (x⁻¹ * w) * w⁻¹ * x⁻¹ := by rw [hcomm.inv_left.eq]
        _ = x⁻¹ := by group
    have hcw' : (x * w * t) * w * (x * w * t)⁻¹ = x ^ 2 * w := by
      calc (x * w * t) * w * (x * w * t)⁻¹ = x * w * (t * w * t⁻¹) * w⁻¹ * x⁻¹ := by group
        _ = x * w * (x ^ 2 * w) * w⁻¹ * x⁻¹ := by rw [hconjw]
        _ = x * (w * x ^ 2) * x⁻¹ := by group
        _ = x * (x ^ 2 * w) * x⁻¹ := by rw [(hcomm.symm.pow_right 2).eq]
        _ = x * x ^ 2 * (w * x⁻¹) := by group
        _ = x * x ^ 2 * (x⁻¹ * w) := by rw [hcomm.inv_left.eq]
        _ = x ^ 2 * w := by group
    have hs2' : (x * w * t) ^ 2 = 1 := by
      calc (x * w * t) ^ 2 = x * w * ((t * x * t⁻¹) * (t * w * t⁻¹)) * t ^ 2 := by
            rw [pow_two, pow_two]; group
        _ = x * w * (x⁻¹ * (x ^ 2 * w)) * x ^ 2 := by rw [hconjx, hconjw, ht2]
        _ = x * (w * x) * (w * x ^ 2) := by group
        _ = x * (x * w) * (w * x ^ 2) := by rw [← hcomm.eq]
        _ = x * x * (w * w) * x ^ 2 := by group
        _ = x * x * 1 * x ^ 2 := by rw [hww]
        _ = x ^ 4 := by group
        _ = 1 := hx4'
    exact hsplit (x * w * t) hsH' hcx' hcw' hs2'
  · -- t² = w : impossible, since conjugation by t fixes t²
    exfalso
    have h1 : t * t ^ 2 * t⁻¹ = t ^ 2 := by group
    rw [ht2, hconjw] at h1
    have h2 : x ^ 2 * w = 1 * w := by rw [one_mul]; exact h1
    exact hx2ne (mul_right_cancel h2)
  · -- t² = x²w : also impossible
    exfalso
    have h1 : t * t ^ 2 * t⁻¹ = t ^ 2 := by group
    rw [ht2] at h1
    have h2 : t * (x ^ 2 * w) * t⁻¹ = w := by
      have h3 : t * (x ^ 2 * w) * t⁻¹ = (t * x ^ 2 * t⁻¹) * (t * w * t⁻¹) := by group
      rw [h3, ← conj_pow, hconjx, hconjw, inv_pow, hx2inv]
      calc x ^ 2 * (x ^ 2 * w) = x ^ 2 * x ^ 2 * w := by group
        _ = w := by
            have h4 : x ^ 2 * x ^ 2 = x ^ 4 := by group
            rw [h4, hx4', one_mul]
    rw [h2] at h1
    have h3 : x ^ 2 * w = 1 * w := by rw [one_mul]; exact h1.symm
    exact hx2ne (mul_right_cancel h3)

/-- The `K₈`-branch of the classification: a nonabelian group of order 16 with no element
of order 8 and a normal subgroup isomorphic to `K₈` is one of `G₈`–`G₁₂`. -/
private lemma classify_of_k8 [Finite G] (hcard : Nat.card G = 16)
    (hnab : ¬ ∀ a b : G, a * b = b * a) (hno8 : ∀ g : G, orderOf g ≠ 8)
    (H : Subgroup G) (hHnorm : H.Normal) (hH8 : Nat.card H = 8) (eH : H ≃* K8g) :
    ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
  classical
  -- transfer the generators of K₈ into G
  have horder : ∀ p : K8g, orderOf ((eH.symm p : H) : G) = orderOf p := by
    intro p
    have h1 : orderOf ((eH.symm p : H) : G) = orderOf (eH.symm p) :=
      orderOf_injective H.subtype H.subtype_injective (eH.symm p)
    have h2 : orderOf (eH.symm p) = orderOf p :=
      orderOf_injective eH.symm.toMonoidHom eH.symm.injective p
    rw [h1, h2]
  obtain ⟨x, w, hxmem, hwmem, hx4, hw2, hcomm, hw_notin, hdecomp⟩ :
      ∃ x w : G, x ∈ H ∧ w ∈ H ∧ orderOf x = 4 ∧ w ^ 2 = 1 ∧ Commute x w ∧
        w ∉ Subgroup.zpowers x ∧
        ∀ h : H, ∃ a b : ℕ, a < 4 ∧ b < 2 ∧ (h : G) = x ^ a * w ^ b := by
    refine ⟨((eH.symm xK8 : H) : G), ((eH.symm yK8 : H) : G), (eH.symm xK8).2,
      (eH.symm yK8).2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [horder, orderOf_xK8]
    · have h1 : orderOf ((eH.symm yK8 : H) : G) = 2 := by rw [horder, orderOf_yK8]
      calc ((eH.symm yK8 : H) : G) ^ 2
          = ((eH.symm yK8 : H) : G) ^ orderOf ((eH.symm yK8 : H) : G) := by rw [h1]
        _ = 1 := pow_orderOf_eq_one _
    · have h1 : eH.symm xK8 * eH.symm yK8 = eH.symm yK8 * eH.symm xK8 := by
        rw [← map_mul, ← map_mul, mul_comm]
      exact congrArg Subtype.val h1
    · intro hmem
      obtain ⟨m, hm_lt, hm⟩ := exists_pow_eq_of_mem_zpowers
        (x := ((eH.symm xK8 : H) : G)) (by rw [horder, orderOf_xK8]; norm_num) hmem
      rw [horder, orderOf_xK8] at hm_lt
      have hm2 : ((eH.symm xK8 ^ m : H) : G) = ((eH.symm yK8 : H) : G) := by
        exact_mod_cast hm
      have hm' : eH.symm xK8 ^ m = eH.symm yK8 := Subtype.coe_injective hm2
      have hK8 : xK8 ^ m = yK8 := by
        have h2 := congrArg eH hm'
        rwa [map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
      interval_cases m <;> exact absurd hK8 (by decide)
    · intro h
      refine ⟨(Multiplicative.toAdd (eH h).1).val, (Multiplicative.toAdd (eH h).2).val,
        ZMod.val_lt _, ZMod.val_lt _, ?_⟩
      have h1 : h = eH.symm xK8 ^ (Multiplicative.toAdd (eH h).1).val *
          eH.symm yK8 ^ (Multiplicative.toAdd (eH h).2).val := by
        conv_lhs => rw [← eH.symm_apply_apply h]
        conv_lhs => rw [k8g_decomp (eH h)]
        rw [map_mul, map_pow, map_pow]
      have h2 := congrArg Subtype.val h1
      simpa using h2
  -- basic power facts
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hx2ne : x ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hx4] at hdvd
    omega
  have hxx3 : x * x ^ 3 = 1 := by
    have h1 : x * x ^ 3 = x ^ 4 := by group
    rw [h1, hx4']
  have hxinv : x⁻¹ = x ^ 3 := inv_eq_of_mul_eq_one_right hxx3
  have hww : w * w = 1 := by rw [← pow_two]; exact hw2
  have hwne1 : w ≠ 1 := by
    intro h
    exact hw_notin (by rw [h]; exact Subgroup.one_mem _)
  -- H is commutative
  have hcommH : ∀ g₁ g₂ : G, g₁ ∈ H → g₂ ∈ H → g₁ * g₂ = g₂ * g₁ := by
    intro g₁ g₂ h₁ h₂
    obtain ⟨a₁, b₁, _, _, he₁⟩ := hdecomp ⟨g₁, h₁⟩
    obtain ⟨a₂, b₂, _, _, he₂⟩ := hdecomp ⟨g₂, h₂⟩
    have he₁' : g₁ = x ^ a₁ * w ^ b₁ := he₁
    have he₂' : g₂ = x ^ a₂ * w ^ b₂ := he₂
    have c1 : Commute (x ^ a₁) (x ^ a₂) := (Commute.refl x).pow_pow _ _
    have c2 : Commute (x ^ a₁) (w ^ b₂) := (hcomm.pow_left _).pow_right _
    have c3 : Commute (w ^ b₁) (x ^ a₂) := (hcomm.symm.pow_left _).pow_right _
    have c4 : Commute (w ^ b₁) (w ^ b₂) := (Commute.refl w).pow_pow _ _
    rw [he₁', he₂']
    exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  -- index-2 complement
  have hHidx : H.index = 2 := by
    have hmul := H.card_mul_index
    rw [hH8, hcard] at hmul
    omega
  obtain ⟨t, ht⟩ : ∃ t : G, t ∉ H := by
    by_contra hc
    push Not at hc
    have htop : H = ⊤ := by
      rw [Subgroup.eq_top_iff']
      exact hc
    rw [htop, Subgroup.card_top, hcard] at hH8
    omega
  have ht2H : t ^ 2 ∈ H := by
    haveI : Finite (G ⧸ H) := Quotient.finite _
    rw [← QuotientGroup.eq_one_iff]
    have hq2 : ((t ^ 2 : G) : G ⧸ H) = ((t : G ⧸ H)) ^ 2 := rfl
    rw [hq2]
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    have hcardQ : Nat.card (G ⧸ H) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hHidx
    rw [← hcardQ]
    exact orderOf_dvd_natCard _
  -- express the conjugates and t² in the generators
  have hτx_mem : t * x * t⁻¹ ∈ H := hHnorm.conj_mem x hxmem t
  have hτw_mem : t * w * t⁻¹ ∈ H := hHnorm.conj_mem w hwmem t
  obtain ⟨a, b, ha4, hb2, hτx0⟩ := hdecomp ⟨_, hτx_mem⟩
  obtain ⟨c, d, hc4, hd2, hτw0⟩ := hdecomp ⟨_, hτw_mem⟩
  obtain ⟨k, l, hk4, hl2, ht20⟩ := hdecomp ⟨_, ht2H⟩
  have hτx' : t * x * t⁻¹ = x ^ a * w ^ b := hτx0
  have hτw' : t * w * t⁻¹ = x ^ c * w ^ d := hτw0
  have ht2' : t ^ 2 = x ^ k * w ^ l := ht20
  clear hτx0 hτw0 ht20
  -- conjugation of squares; involutivity of conjugation by t on H
  have hconj_sq : ∀ g : G, t * g ^ 2 * t⁻¹ = (t * g * t⁻¹) ^ 2 := by
    intro g
    rw [← conj_pow]
  have htau2 : ∀ g : G, g ∈ H → t * (t * g * t⁻¹) * t⁻¹ = g := by
    intro g hg
    have h1 : t ^ 2 * g = g * t ^ 2 := hcommH _ _ ht2H hg
    calc t * (t * g * t⁻¹) * t⁻¹ = t ^ 2 * g * (t ^ 2)⁻¹ := by rw [pow_two]; group
      _ = g * t ^ 2 * (t ^ 2)⁻¹ := by rw [h1]
      _ = g := by group
  -- squares of the K₈ words
  have hsq_ab : ∀ a' b' : ℕ, (x ^ a' * w ^ b') ^ 2 = x ^ (a' * 2) * w ^ (b' * 2) := by
    intro a' b'
    have hc : Commute (x ^ a') (w ^ b') := (hcomm.pow_left _).pow_right _
    rw [hc.mul_pow, ← pow_mul, ← pow_mul]
  have hwb : ∀ b' : ℕ, w ^ (b' * 2) = 1 := by
    intro b'
    rw [mul_comm, pow_mul, hw2, one_pow]
  -- the exponent a is odd
  have ha_odd : a = 1 ∨ a = 3 := by
    by_contra hcon
    push Not at hcon
    have ha02 : a = 0 ∨ a = 2 := by omega
    have h1 : t * x ^ 2 * t⁻¹ = x ^ (a * 2) := by
      rw [hconj_sq, hτx', hsq_ab, hwb, mul_one]
    have h2 : x ^ (a * 2) = 1 := by
      rcases ha02 with rfl | rfl
      · rw [zero_mul, pow_zero]
      · rw [show (2 * 2 : ℕ) = 4 from rfl]
        exact hx4'
    rw [h2] at h1
    have h3 : x ^ 2 = 1 := by
      calc x ^ 2 = t⁻¹ * (t * x ^ 2 * t⁻¹) * t := by group
        _ = t⁻¹ * 1 * t := by rw [h1]
        _ = 1 := by group
    exact hx2ne h3
  -- the conjugate of w is w or x²w
  have hτw_cases : t * w * t⁻¹ = w ∨ t * w * t⁻¹ = x ^ 2 * w := by
    have h1 : t * w ^ 2 * t⁻¹ = x ^ (c * 2) * w ^ (d * 2) := by
      rw [hconj_sq, hτw', hsq_ab]
    have h2 : x ^ (c * 2) = 1 := by
      calc x ^ (c * 2) = x ^ (c * 2) * w ^ (d * 2) := by rw [hwb, mul_one]
        _ = t * w ^ 2 * t⁻¹ := h1.symm
        _ = 1 := by rw [hw2]; group
    have hdvd : (4 : ℕ) ∣ c * 2 := by
      rw [← hx4]
      exact orderOf_dvd_of_pow_eq_one h2
    have hc02 : c = 0 ∨ c = 2 := by omega
    have hd1 : d = 1 := by
      by_contra hd
      have hd0 : d = 0 := by omega
      subst hd0
      rw [pow_zero, mul_one] at hτw'
      rcases hc02 with rfl | rfl
      · rw [pow_zero] at hτw'
        apply hwne1
        calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
          _ = t⁻¹ * 1 * t := by rw [hτw']
          _ = 1 := by group
      · have h3 : w = x ^ (a * 2) := by
          calc w = t * (t * w * t⁻¹) * t⁻¹ := (htau2 w hwmem).symm
            _ = t * x ^ 2 * t⁻¹ := by rw [hτw']
            _ = (t * x * t⁻¹) ^ 2 := hconj_sq x
            _ = (x ^ a * w ^ b) ^ 2 := by rw [hτx']
            _ = x ^ (a * 2) * w ^ (b * 2) := hsq_ab a b
            _ = x ^ (a * 2) := by rw [hwb, mul_one]
        exact hw_notin (by rw [h3]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
    subst hd1
    rw [pow_one] at hτw'
    rcases hc02 with rfl | rfl
    · left
      rw [pow_zero, one_mul] at hτw'
      exact hτw'
    · right
      exact hτw'
  -- t² lies in {1, x², w, x²w}
  have ht2_cases : t ^ 2 = 1 ∨ t ^ 2 = x ^ 2 ∨ t ^ 2 = w ∨ t ^ 2 = x ^ 2 * w := by
    have hk_even : k = 0 ∨ k = 2 := by
      by_contra hcon
      push Not at hcon
      have hk13 : k = 1 ∨ k = 3 := by omega
      apply hno8 t
      have ht4 : t ^ 4 = x ^ (k * 2) := by
        have h1 : t ^ 4 = (t ^ 2) ^ 2 := by group
        rw [h1, ht2', hsq_ab, hwb, mul_one]
      have ht4ne : t ^ 4 ≠ 1 := by
        rw [ht4]
        rcases hk13 with rfl | rfl
        · rw [show (1 * 2 : ℕ) = 2 from rfl]
          exact hx2ne
        · rw [show (3 * 2 : ℕ) = 6 from rfl]
          intro h
          have hdvd : (4 : ℕ) ∣ 6 := by
            rw [← hx4]
            exact orderOf_dvd_of_pow_eq_one h
          omega
      have ht8 : t ^ 8 = 1 := by
        have h1 : t ^ 8 = (t ^ 4) ^ 2 := by group
        rw [h1, ht4, ← pow_mul]
        rcases hk13 with rfl | rfl
        · rw [show (1 * 2 * 2 : ℕ) = 4 from rfl]
          exact hx4'
        · rw [show (3 * 2 * 2 : ℕ) = 12 from rfl]
          have h2 : (x ^ 12 : G) = (x ^ 4) ^ 3 := by group
          rw [h2, hx4', one_pow]
      have hdvd8 : orderOf t ∣ 8 := orderOf_dvd_of_pow_eq_one ht8
      have hndvd4 : ¬ orderOf t ∣ 4 := fun hd => ht4ne (orderOf_dvd_iff_pow_eq_one.mp hd)
      have hmem : orderOf t ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd8, by norm_num⟩
      rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h
      · exact absurd (by rw [h]; norm_num : orderOf t ∣ 4) hndvd4
      · exact absurd (by rw [h]; norm_num : orderOf t ∣ 4) hndvd4
      · exact absurd (by rw [h] : orderOf t ∣ 4) hndvd4
      · exact h
    have hl01 : l = 0 ∨ l = 1 := by omega
    rcases hk_even with rfl | rfl
    · rcases hl01 with rfl | rfl
      · left
        rw [ht2', pow_zero, pow_zero, one_mul]
      · right; right; left
        rw [ht2', pow_zero, pow_one, one_mul]
    · rcases hl01 with rfl | rfl
      · right; left
        rw [ht2', pow_zero, mul_one]
      · right; right; right
        rw [ht2', pow_one]
  -- eight ψ-shapes
  have hb01 : b = 0 ∨ b = 1 := by omega
  rcases hτw_cases with hcw | hcw
  · -- τ w = w
    rcases ha_odd with rfl | rfl
    · rcases hb01 with rfl | rfl
      · -- ψ₁ : t centralizes H, so G is abelian — contradiction
        exfalso
        rw [pow_one, pow_zero, mul_one] at hτx'
        apply hnab
        have hcommt : ∀ g : G, g ∈ H → Commute t g := by
          intro g hg
          obtain ⟨a', b', _, _, he⟩ := hdecomp ⟨g, hg⟩
          have he' : g = x ^ a' * w ^ b' := he
          have h1 : Commute t x := by
            have h2 : t * x = x * t := by
              calc t * x = t * x * t⁻¹ * t := by group
                _ = x * t := by rw [hτx']
            exact h2
          have h2 : Commute t w := by
            have h3 : t * w = w * t := by
              calc t * w = t * w * t⁻¹ * t := by group
                _ = w * t := by rw [hcw]
            exact h3
          rw [he']
          exact (h1.pow_right _).mul_right (h2.pow_right _)
        intro g₁ g₂
        rcases decomp_index_two hHidx ht g₁ with h₁ | ⟨p, hp, rfl⟩
        · rcases decomp_index_two hHidx ht g₂ with h₂ | ⟨q, hq, rfl⟩
          · exact hcommH _ _ h₁ h₂
          · have c1 : Commute g₁ q := hcommH _ _ h₁ hq
            have c2 : Commute g₁ t := (hcommt g₁ h₁).symm
            exact (c1.mul_right c2).eq
        · rcases decomp_index_two hHidx ht g₂ with h₂ | ⟨q, hq, rfl⟩
          · have c1 : Commute p g₂ := hcommH _ _ hp h₂
            have c2 : Commute t g₂ := hcommt g₂ h₂
            exact (c1.mul_left c2).eq
          · have cpq : Commute p q := hcommH _ _ hp hq
            have cpt : Commute t p := hcommt p hp
            have cqt : Commute t q := hcommt q hq
            exact ((cpq.mul_right cpt.symm).mul_left
              (cqt.mul_right (Commute.refl t))).eq
      · -- ψ₅-form directly
        rw [pow_one, pow_one] at hτx'
        exact classify_k8_psi5 hcard x w t H hxmem hwmem ht hx4 hw2 hcomm hw_notin
          hτx' hcw ht2_cases
    · rcases hb01 with rfl | rfl
      · -- ψ₃-form directly
        rw [pow_zero, mul_one] at hτx'
        have hτx'' : t * x * t⁻¹ = x⁻¹ := by rw [hτx', ← hxinv]
        exact classify_k8_psi3 hcard x w t H hxmem hwmem ht hx4 hw2 hcomm hw_notin
          hτx'' hcw ht2_cases
      · -- ψ₇ : rebase the involution to x²w, giving a ψ₅-form
        rw [pow_one] at hτx'
        have hw'mem : x ^ 2 * w ∈ H := H.mul_mem (H.pow_mem hxmem 2) hwmem
        have hw'2 : (x ^ 2 * w) ^ 2 = 1 := by
          rw [(hcomm.pow_left 2).mul_pow, hw2, mul_one]
          have h1 : ((x ^ 2) ^ 2 : G) = x ^ 4 := by group
          rw [h1, hx4']
        have hw'_notin : x ^ 2 * w ∉ Subgroup.zpowers x := by
          intro hmem
          apply hw_notin
          have h1 : w = (x ^ 2)⁻¹ * (x ^ 2 * w) := by group
          rw [h1]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _
            (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)) hmem
        have hcomm' : Commute x (x ^ 2 * w) := ((Commute.refl x).pow_right 2).mul_right hcomm
        have hτx_new : t * x * t⁻¹ = x * (x ^ 2 * w) := by
          rw [hτx']
          group
        have hsq31 : (x ^ 3 * w) ^ 2 = x ^ 2 := by
          rw [(hcomm.pow_left 3).mul_pow, hw2, mul_one]
          have h1 : ((x ^ 3) ^ 2 : G) = x ^ 4 * x ^ 2 := by group
          rw [h1, hx4', one_mul]
        have hτw_new : t * (x ^ 2 * w) * t⁻¹ = x ^ 2 * w := by
          have h1 : t * (x ^ 2 * w) * t⁻¹ = (t * x ^ 2 * t⁻¹) * (t * w * t⁻¹) := by group
          rw [h1, hconj_sq, hτx', hcw, hsq31]
        have hx4w : x ^ 2 * (x ^ 2 * w) = w := by
          calc x ^ 2 * (x ^ 2 * w) = x ^ 2 * x ^ 2 * w := by group
            _ = w := by
                have h1 : (x ^ 2 * x ^ 2 : G) = x ^ 4 := by group
                rw [h1, hx4', one_mul]
        have ht2v' : t ^ 2 = 1 ∨ t ^ 2 = x ^ 2 ∨ t ^ 2 = x ^ 2 * w ∨
            t ^ 2 = x ^ 2 * (x ^ 2 * w) := by
          rcases ht2_cases with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · refine Or.inr (Or.inr (Or.inr ?_))
            rw [h, hx4w]
          · exact Or.inr (Or.inr (Or.inl h))
        exact classify_k8_psi5 hcard x (x ^ 2 * w) t H hxmem hw'mem ht hx4 hw'2 hcomm'
          hw'_notin hτx_new hτw_new ht2v'
  · -- τ w = x² w
    rcases ha_odd with rfl | rfl
    · rcases hb01 with rfl | rfl
      · -- ψ₈ : rebase the order-4 generator to x w, giving a ψ₆-form
        rw [pow_one, pow_zero, mul_one] at hτx'
        have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
        have hx'2 : (x * w) ^ 2 = x ^ 2 := by
          rw [hcomm.mul_pow, hw2, mul_one]
        have hx'4 : (x * w) ^ 4 = 1 := by
          rw [hcomm.mul_pow, hx4', one_mul]
          have h1 : (w ^ 4 : G) = (w ^ 2) ^ 2 := by group
          rw [h1, hw2, one_pow]
        have hx'ord : orderOf (x * w) = 4 := by
          have hdvd : orderOf (x * w) ∣ 4 := orderOf_dvd_of_pow_eq_one hx'4
          have hne2 : ¬ orderOf (x * w) ∣ 2 := by
            intro hd
            have h2 : (x * w) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
            rw [hx'2] at h2
            exact hx2ne h2
          have hmem4 : orderOf (x * w) ∈ Nat.divisors 4 :=
            Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
          rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hmem4
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem4
          rcases hmem4 with h | h | h
          · exact absurd (by rw [h]; norm_num : orderOf (x * w) ∣ 2) hne2
          · exact absurd (by rw [h] : orderOf (x * w) ∣ 2) hne2
          · exact h
        have hw_notin' : w ∉ Subgroup.zpowers (x * w) := by
          intro hmem
          obtain ⟨m, hm_lt, hm⟩ := exists_pow_eq_of_mem_zpowers
            (by rw [hx'ord]; norm_num) hmem
          rw [hx'ord] at hm_lt
          rw [hcomm.mul_pow] at hm
          interval_cases m
          · rw [pow_zero, pow_zero, one_mul] at hm
            exact hwne1 hm.symm
          · rw [pow_one, pow_one] at hm
            have hx1 : x = 1 := by
              have h1 : x * w = 1 * w := by rw [one_mul]; exact hm
              exact mul_right_cancel h1
            apply hx2ne
            rw [hx1, one_pow]
          · rw [hw2, mul_one] at hm
            apply hw_notin
            rw [← hm]
            exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2
          · have hw3 : w ^ 3 = w := by
              have h1 : (w ^ 3 : G) = w ^ 2 * w := by group
              rw [h1, hw2, one_mul]
            rw [hw3] at hm
            have hx3 : x ^ 3 = 1 := by
              have h1 : x ^ 3 * w = 1 * w := by rw [one_mul]; exact hm
              exact mul_right_cancel h1
            have hdvd : (4 : ℕ) ∣ 3 := by
              rw [← hx4]
              exact orderOf_dvd_of_pow_eq_one hx3
            omega
        have hx'inv : (x * w)⁻¹ = x ^ 3 * w := by
          rw [mul_inv_rev, hwinv, hxinv]
          exact (hcomm.symm.pow_right 3).eq
        have hτx_new : t * (x * w) * t⁻¹ = (x * w)⁻¹ := by
          have h1 : t * (x * w) * t⁻¹ = (t * x * t⁻¹) * (t * w * t⁻¹) := by group
          rw [h1, hτx', hcw, hx'inv]
          group
        have hτw_new : t * w * t⁻¹ = (x * w) ^ 2 * w := by
          rw [hcw, hx'2]
        have ht2v' : t ^ 2 = 1 ∨ t ^ 2 = (x * w) ^ 2 ∨ t ^ 2 = w ∨
            t ^ 2 = (x * w) ^ 2 * w := by
          rcases ht2_cases with h | h | h | h
          · exact Or.inl h
          · refine Or.inr (Or.inl ?_)
            rw [h, hx'2]
          · exact Or.inr (Or.inr (Or.inl h))
          · refine Or.inr (Or.inr (Or.inr ?_))
            rw [h, hx'2]
        exact classify_k8_psi6 hcard (x * w) w t H (H.mul_mem hxmem hwmem) hwmem ht
          hx'ord hw2 (hcomm.mul_left (Commute.refl w)) hw_notin' hτx_new hτw_new ht2v'
      · -- ψ₄ : impossible, conjugation by t would not be involutive
        rw [pow_one, pow_one] at hτx'
        exfalso
        have h1 : x = (x * w) * (x ^ 2 * w) := by
          calc x = t * (t * x * t⁻¹) * t⁻¹ := (htau2 x hxmem).symm
            _ = t * (x * w) * t⁻¹ := by rw [hτx']
            _ = (t * x * t⁻¹) * (t * w * t⁻¹) := by group
            _ = (x * w) * (x ^ 2 * w) := by rw [hτx', hcw]
        have h2 : (x * w) * (x ^ 2 * w) = x ^ 3 := by
          calc (x * w) * (x ^ 2 * w) = x * (w * x ^ 2) * w := by group
            _ = x * (x ^ 2 * w) * w := by rw [(hcomm.symm.pow_right 2).eq]
            _ = x * x ^ 2 * (w * w) := by group
            _ = x * x ^ 2 * 1 := by rw [hww]
            _ = x ^ 3 := by group
        rw [h2] at h1
        have h3 : x ^ 2 = 1 := by
          have h4 : x * x ^ 2 = x * 1 := by
            rw [mul_one]
            have h5 : x * x ^ 2 = x ^ 3 := by group
            rw [h5, ← h1]
          exact mul_left_cancel h4
        exact hx2ne h3
    · rcases hb01 with rfl | rfl
      · -- ψ₆-form directly
        rw [pow_zero, mul_one] at hτx'
        have hτx'' : t * x * t⁻¹ = x⁻¹ := by rw [hτx', ← hxinv]
        exact classify_k8_psi6 hcard x w t H hxmem hwmem ht hx4 hw2 hcomm hw_notin
          hτx'' hcw ht2_cases
      · -- ψ₂ : impossible, conjugation by t would not be involutive
        rw [pow_one] at hτx'
        exfalso
        have h1 : x = (x ^ 3 * w) ^ 3 * (x ^ 2 * w) := by
          calc x = t * (t * x * t⁻¹) * t⁻¹ := (htau2 x hxmem).symm
            _ = t * (x ^ 3 * w) * t⁻¹ := by rw [hτx']
            _ = (t * x ^ 3 * t⁻¹) * (t * w * t⁻¹) := by group
            _ = (t * x * t⁻¹) ^ 3 * (t * w * t⁻¹) := by rw [← conj_pow]
            _ = (x ^ 3 * w) ^ 3 * (x ^ 2 * w) := by rw [hτx', hcw]
        have h2 : (x ^ 3 * w) ^ 3 * (x ^ 2 * w) = x ^ 3 := by
          have h3 : (x ^ 3 * w) ^ 3 = x ^ 9 * w := by
            rw [(hcomm.pow_left 3).mul_pow]
            have h4 : ((x ^ 3) ^ 3 : G) = x ^ 9 := by group
            have h5 : (w ^ 3 : G) = w := by
              have h6 : (w ^ 3 : G) = w ^ 2 * w := by group
              rw [h6, hw2, one_mul]
            rw [h4, h5]
          rw [h3]
          calc x ^ 9 * w * (x ^ 2 * w) = x ^ 9 * (w * x ^ 2) * w := by group
            _ = x ^ 9 * (x ^ 2 * w) * w := by rw [(hcomm.symm.pow_right 2).eq]
            _ = x ^ 9 * x ^ 2 * (w * w) := by group
            _ = x ^ 9 * x ^ 2 * 1 := by rw [hww]
            _ = x ^ 11 := by group
            _ = x ^ 3 := by
                have h7 : (x ^ 11 : G) = (x ^ 4) ^ 2 * x ^ 3 := by group
                rw [h7, hx4', one_pow, one_mul]
        rw [h2] at h1
        have h3 : x ^ 2 = 1 := by
          have h4 : x * x ^ 2 = x * 1 := by
            rw [mul_one]
            have h5 : x * x ^ 2 = x ^ 3 := by group
            rw [h5, ← h1]
          exact mul_left_cancel h4
        exact hx2ne h3

end ClassifyK8

/-! ### Main classification theorem

Every group of order 16 is isomorphic to exactly one of the 14 representatives:
the abelian case is handled by the `p⁴` engine, and the nonabelian case splits into
the `C₈`-extension branch and the `K₈`-extension branch, following Wild.
-/

/-- **Completeness.** Every group of order 16 is isomorphic to one of the 14 representatives. -/
theorem order16_wild_classification {G : Type*} [Group G]
    (hcard : Nat.card G = 16) : ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
  classical
  haveI : Finite G := by
    by_contra hinf
    haveI : Infinite G := ⟨hinf⟩
    have h0 : Nat.card G = 0 := Nat.card_eq_zero_of_infinite
    rw [hcard] at h0
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hab : ∀ a b : G, a * b = b * a
  · -- abelian: five classes via the p⁴ engine
    letI : CommGroup G := { ‹Group G› with mul_comm := hab }
    obtain ⟨i, ⟨e⟩⟩ := orderP4Abel_complete 2 G (by rw [hcard]; norm_num)
    fin_cases i
    · exact ⟨6, ⟨e⟩⟩
    · obtain ⟨e2⟩ := order16_A2_iso_concrete
      exact ⟨1, ⟨e.trans e2⟩⟩
    · exact ⟨13, ⟨e⟩⟩
    · obtain ⟨e4⟩ := order16_A4_iso_concrete
      exact ⟨7, ⟨e.trans e4⟩⟩
    · exact ⟨0, ⟨e⟩⟩
  · by_cases h8 : ∃ g : G, orderOf g = 8
    · -- C₈-extension branch
      obtain ⟨g, hg⟩ := h8
      exact classify_of_order8 hcard hab g hg
    · -- K₈-extension branch
      push Not at h8
      have hnotG0 : ¬ Nonempty (G ≃* order16_wild_G0) := by
        rintro ⟨e⟩
        apply hab
        intro a b
        apply e.injective
        rw [map_mul, map_mul, mul_comm]
      rcases lemma_normal_c8_or_k8 hcard hnotG0 with
        ⟨H, _, hcardH, ⟨eC⟩⟩ | ⟨H, hn, hcardH, ⟨eK⟩⟩
      · -- a normal C₈ would give an element of order 8
        exfalso
        have h1 : orderOf ((eC.symm xC8 : H) : G) = 8 := by
          have h2 : orderOf ((eC.symm xC8 : H) : G) = orderOf (eC.symm xC8) :=
            orderOf_injective H.subtype H.subtype_injective (eC.symm xC8)
          have h3 : orderOf (eC.symm xC8) = orderOf xC8 :=
            orderOf_injective eC.symm.toMonoidHom eC.symm.injective xC8
          rw [h2, h3, orderOf_xC8]
        exact h8 _ h1
      · exact classify_of_k8 hcard hab h8 H hn hcardH eK

/-- **Distinctness.** The 14 representatives are pairwise non-isomorphic. -/
theorem order16_wild_distinct {i j : Fin 14}
    (h : Nonempty (order16_wild_reps i ≃* order16_wild_reps j)) : i = j := by
  obtain ⟨e⟩ := h
  have hinv : order16_wild_invariant i = order16_wild_invariant j := by
    rw [← order16_wild_invariant_spec i, ← order16_wild_invariant_spec j]
    exact wildInvariantOf_eq_of_mulEquiv e
  have hinj : Function.Injective order16_wild_invariant := by decide
  exact hinj hinv

/-- The 14 representatives are pairwise non-isomorphic (the `IsClassif` form). -/
theorem order16_wild_pairwise_noniso : PairwiseNonMulEquiv order16_wild_reps := by
  intro i j hiso
  exact order16_wild_distinct hiso

set_option linter.unusedVariables false in
/-- There are exactly 14 groups of order 16. -/
theorem order16_wild_isClassif : IsClassif 16 order16_wild_reps :=
  { card := card_order16_wild_reps
    complete := fun G _ hG => order16_wild_classification hG
    distinct := fun i j h => order16_wild_distinct h
  }

end Smallgroups.UsefulTheorems
