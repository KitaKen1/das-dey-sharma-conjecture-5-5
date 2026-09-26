/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.Order2PSq
import Order16Library.UsefulTheorems.P3Group
import Order16Library.UsefulTheorems.Counting
import Order16Library.UsefulTheorems.CenterInvariant
import Order16Library.UsefulTheorems.SchurZassenhaus
import Order16Library.UsefulTheorems.SemidirectProductClassify
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

/-!
# First reductions for groups of order 88

Since `88 = 8 * 11`, the Sylow `11`-subgroup is normal.  Thus every group of
order `88` splits as `C₁₁ ⋊ H`, where `H` is a group of order `8`.

This file records that reduction and the twelve expected semidirect-product
representatives.  The remaining classification work is the orbit calculation
for homomorphisms `H → Aut(C₁₁)`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Sylow-11 normality and semidirect-product reduction -/

/-- The Sylow `11`-subgroup is unique in a group of order `88`. -/
theorem card_sylow_11_eq_one_of_card_88 [Finite G] (hG : Nat.card G = 88) :
    Nat.card (Sylow 11 G) = 1 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 11 G))
  have hndvd_11 : ¬ 11 ∣ Nat.card (Sylow 11 G) := not_dvd_card_sylow 11 G
  have hdvd88 : Nat.card (Sylow 11 G) ∣ 88 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h88 : 88 = 8 * 11 := by norm_num
  have hdvd8_mul : Nat.card (Sylow 11 G) ∣ 8 * 11 := by
    simpa [h88] using hdvd88
  have hp11 : Nat.Prime 11 := by norm_num
  have hcop : Nat.Coprime (Nat.card (Sylow 11 G)) 11 :=
    (hp11.coprime_iff_not_dvd.mpr hndvd_11).symm
  have hdvd8 : Nat.card (Sylow 11 G) ∣ 8 := hcop.dvd_of_dvd_mul_right hdvd8_mul
  have hmod := card_sylow_modEq_one 11 G
  have hle : Nat.card (Sylow 11 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
  have hpos : 0 < Nat.card (Sylow 11 G) := Nat.card_pos
  have hlt : Nat.card (Sylow 11 G) < 11 := by omega
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 1 < 11)] at hmod
  exact hmod

/-- The Sylow `11`-subgroup of a group of order `88` is normal. -/
theorem sylow_11_normal_of_card_88 [Finite G] (hG : Nat.card G = 88) (P : Sylow 11 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 11 G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_11_eq_one_of_card_88 hG)).1
  exact normal_of_subsingleton P

/-- The Sylow `11`-subgroup of a group of order `88` has order `11`. -/
theorem card_sylow_11_subgroup_of_card_88 [Finite G] (hG : Nat.card G = 88)
    (P : Sylow 11 G) : Nat.card (↑P : Subgroup G) = 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hndvd : ¬ 11 ∣ 8 := by norm_num
  have hfact : (88 : ℕ).factorization 11 = 1 := by
    rw [show 88 = 8 * 11 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 11), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur-Zassenhaus reduction for order `88`.**
Every group of order `88` is a semidirect product `N ⋊[φ] H`, where
`N` has order `11` and `H` has order `8`. -/
theorem order88_semidirectProduct [Finite G] (hG : Nat.card G = 88) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = 11 ∧ Nat.card H = 8 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 11 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_11_normal_of_card_88 hG P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 11 :=
    card_sylow_11_subgroup_of_card_88 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    exact (show Nat.Prime 11 by norm_num).coprime_iff_not_dvd.mpr this
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 8 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 11 * Nat.card H = 11 * 8 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 11) h1'
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

/-! ### Candidate representatives -/

/-- The normal subgroup in the order-`88` representatives. -/
abbrev order88_C11 : Type := CyclicRep 11

/-- `C₈`. -/
abbrev order88_C8 : Type := Multiplicative (ZMod 8)
/-- `C₄ × C₂`. -/
abbrev order88_C4C2 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
/-- `C₂ × C₂ × C₂`. -/
abbrev order88_C2C2C2 : Type :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
/-- The dihedral group of order `8`. -/
abbrev order88_D8 : Type := DihedralGroup 4
/-- The quaternion group of order `8`. -/
abbrev order88_Q8 : Type := QuaternionGroup 2

/-- The reduction map `ZMod n → ZMod m`, viewed multiplicatively. -/
noncomputable def zmodCastMulHom {m n : ℕ} (h : m ∣ n) :
    Multiplicative (ZMod n) →* Multiplicative (ZMod m) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod m)).toAddMonoidHom

/-! ### Automorphisms of `C₁₁` with 8-power equal to one -/

/-- The standard map from units of `ZMod 11` to automorphisms of `C₁₁` is injective. -/
theorem order88_unitAutHom_injective :
    Function.Injective (unitAutHom (p := 11)) := by
  intro u v h
  have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod 11)) =
      unitAutHom v (Multiplicative.ofAdd (1 : ZMod 11)) := by rw [h]
  simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
  exact Units.ext h1

/-- Every automorphism of `C₁₁` is multiplication by a unit of `ZMod 11`. -/
theorem order88_mulAut_eq_unitAutHom (σ : MulAut order88_C11) :
    ∃ u : (ZMod 11)ˣ, σ = unitAutHom u := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let u_val : ZMod 11 := (σ (Multiplicative.ofAdd (1 : ZMod 11))).toAdd
  have hu_ne_zero : u_val ≠ 0 := by
    intro hz
    have h0 : σ (Multiplicative.ofAdd (0 : ZMod 11)) = Multiplicative.ofAdd (0 : ZMod 11) := by
      calc
        σ (Multiplicative.ofAdd (0 : ZMod 11)) = σ 1 := by simp
        _ = 1 := map_one σ
        _ = Multiplicative.ofAdd (0 : ZMod 11) := by simp
    have h1 : σ (Multiplicative.ofAdd (1 : ZMod 11)) = Multiplicative.ofAdd (0 : ZMod 11) := by
      calc
        σ (Multiplicative.ofAdd (1 : ZMod 11)) = Multiplicative.ofAdd u_val := rfl
        _ = Multiplicative.ofAdd (0 : ZMod 11) := by rw [hz]
    have h01 : Multiplicative.ofAdd (0 : ZMod 11) ≠ Multiplicative.ofAdd (1 : ZMod 11) := by
      intro h
      apply_fun Multiplicative.toAdd at h
      simp at h
    apply h01
    exact σ.injective (h0.trans h1.symm)
  have h_inv : u_val⁻¹ * u_val = 1 := inv_mul_cancel₀ hu_ne_zero
  have h_mul : u_val * u_val⁻¹ = 1 := mul_inv_cancel₀ hu_ne_zero
  let u : (ZMod 11)ˣ := Units.mk u_val (u_val⁻¹) h_mul h_inv
  refine ⟨u, ?_⟩
  apply MulEquiv.ext
  intro x
  let n := Multiplicative.toAdd x
  have hx : Multiplicative.ofAdd n = x := ofAdd_toAdd x
  rw [← hx]
  calc
    σ (Multiplicative.ofAdd n) = σ ((Multiplicative.ofAdd (1 : ZMod 11)) ^ n.val) := by
      rw [show (Multiplicative.ofAdd n : Multiplicative (ZMod 11)) =
          (Multiplicative.ofAdd (1 : ZMod 11)) ^ n.val from by
        calc
          Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 11)) := by
            rw [ZMod.natCast_zmod_val]
          _ = Multiplicative.ofAdd (n.val • (1 : ZMod 11)) := by simp
          _ = (Multiplicative.ofAdd (1 : ZMod 11)) ^ n.val := by
            rw [ofAdd_nsmul]]
    _ = (σ (Multiplicative.ofAdd (1 : ZMod 11))) ^ n.val := by rw [map_pow]
    _ = (Multiplicative.ofAdd u_val) ^ n.val := rfl
    _ = Multiplicative.ofAdd (n.val • u_val) := by rw [← ofAdd_nsmul]
    _ = Multiplicative.ofAdd (u_val * (n.val : ZMod 11)) := by
      rw [nsmul_eq_mul, mul_comm]
    _ = Multiplicative.ofAdd (u_val * n) := by rw [ZMod.natCast_zmod_val]
    _ = unitAutHom u (Multiplicative.ofAdd n) := by rw [unitAutHom_apply]

/-- Multiplication by `-1` on `C₁₁` is inversion. -/
theorem order88_unitAutHom_neg_one :
    unitAutHom (-1 : (ZMod 11)ˣ) = invAut order88_C11 := by
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [unitAutHom_apply, invAut_apply]
  simp

/-- A unit of `ZMod 11` whose eighth power is `1` is `1` or `-1`. -/
theorem order88_unit_pow8_eq_one (u : (ZMod 11)ˣ) (hu : u ^ 8 = 1) :
    u = 1 ∨ u = -1 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have horder_dvd8 : orderOf u ∣ 8 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hu
  have horder_dvd10 : orderOf u ∣ 10 := by
    have h := orderOf_dvd_card (x := u)
    rw [ZMod.card_units 11] at h
    norm_num at h ⊢
    exact h
  have horder_dvd2 : orderOf u ∣ 2 := by
    exact Nat.dvd_gcd horder_dvd8 horder_dvd10
  have horder_pos : 0 < orderOf u := orderOf_pos u
  have horder_cases : orderOf u = 1 ∨ orderOf u = 2 := by
    have hle : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) horder_dvd2
    omega
  rcases horder_cases with h1 | h2
  · exact Or.inl (orderOf_eq_one_iff.mp h1)
  · right
    have hu2 : u ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h2]
    have hval_sq : ((u : ZMod 11) ^ 2) = 1 := by
      exact congrArg Units.val hu2
    have hprod : ((u : ZMod 11) - 1) * ((u : ZMod 11) + 1) = 0 := by
      calc
        ((u : ZMod 11) - 1) * ((u : ZMod 11) + 1) = (u : ZMod 11) ^ 2 - 1 := by ring
        _ = 0 := by rw [hval_sq]; ring
    rcases mul_eq_zero.mp hprod with hu_one | hu_neg
    · have : u = 1 := Units.ext (sub_eq_zero.mp hu_one)
      have hnot : orderOf u ≠ 1 := by omega
      exact (hnot (by rw [this]; simp)).elim
    · exact Units.ext (eq_neg_of_add_eq_zero_left hu_neg)

/-- Any automorphism of `C₁₁` whose eighth power is `1` is trivial or inversion. -/
theorem order88_mulAut_pow8_eq_one_or_inv (α : MulAut order88_C11) (hα : α ^ 8 = 1) :
    α = 1 ∨ α = invAut order88_C11 := by
  obtain ⟨u, hu⟩ := order88_mulAut_eq_unitAutHom α
  have hu8 : u ^ 8 = 1 := by
    apply order88_unitAutHom_injective
    rw [map_pow, ← hu, hα, map_one]
  rcases order88_unit_pow8_eq_one u hu8 with h1 | hneg
  · left
    rw [hu, h1, map_one]
  · right
    rw [hu, hneg, order88_unitAutHom_neg_one]

/-- If `H` has order `8`, every value of an action `H → Aut(C₁₁)` is trivial or inversion. -/
theorem order88_action_value_eq_one_or_inv {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order88_C11) (h : H) :
    φ h = 1 ∨ φ h = invAut order88_C11 := by
  apply order88_mulAut_pow8_eq_one_or_inv
  have hh8 : h ^ 8 = 1 := by
    simpa [hH] using (pow_card_eq_one' (x := h))
  rw [← map_pow, hh8, map_one]

/-- Inversion is not the identity automorphism of `C₁₁`. -/
theorem order88_invAut_ne_one : invAut order88_C11 ≠ 1 := by
  haveI : Fact (1 < 11) := ⟨by norm_num⟩
  intro h
  have hx := congrArg
    (fun f : MulAut order88_C11 => f (Multiplicative.ofAdd (1 : ZMod 11))) h
  have hx' : (Multiplicative.ofAdd (1 : ZMod 11))⁻¹ =
      Multiplicative.ofAdd (1 : ZMod 11) := by
    simpa [invAut_apply] using hx
  clear hx
  have hxadd : (-1 : ZMod 11) = 1 := by
    simpa using congrArg Multiplicative.toAdd hx'
  have hv := congrArg ZMod.val hxadd
  rw [ZMod.val_one] at hv
  norm_num at hv

/-- The character `H → C₂` attached to an order-`88` action `H → Aut(C₁₁)`. -/
noncomputable def order88_actionCharacter {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order88_C11) :
    H →* Multiplicative (ZMod 2) where
  toFun h := by
    classical
    exact if φ h = 1 then 1 else Multiplicative.ofAdd (1 : ZMod 2)
  map_one' := by
    classical
    simp
  map_mul' := by
    classical
    intro a b
    rcases order88_action_value_eq_one_or_inv hH φ a with ha | ha <;>
      rcases order88_action_value_eq_one_or_inv hH φ b with hb | hb
    · have hab : φ (a * b) = 1 := by rw [map_mul, ha, hb, mul_one]
      simp [hab, ha, hb]
    · have hab : φ (a * b) = invAut order88_C11 := by rw [map_mul, ha, hb, one_mul]
      simp [hab, ha, hb, order88_invAut_ne_one]
    · have hab : φ (a * b) = invAut order88_C11 := by rw [map_mul, ha, hb, mul_one]
      simp [hab, ha, hb, order88_invAut_ne_one]
    · have hab : φ (a * b) = 1 := by
        rw [map_mul, ha, hb, ← sq, invAut_sq]
      simp only [hab, ha, hb, order88_invAut_ne_one, if_true, if_false]
      decide

/-- Every element of `C₂` is either `0` or `1`, multiplicatively. -/
theorem order88_c2_element_cases (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  fin_cases m
  · left
    rfl
  · right
    rfl

/-- Every element of `C₂` squares to one. -/
theorem order88_c2_mul_self (x : Multiplicative (ZMod 2)) : x * x = 1 := by
  rcases order88_c2_element_cases x with h | h <;> rw [h] <;> decide

/-- Homomorphisms out of `C₈` are determined by the additive generator `1`. -/
theorem order88_c8_hom_ext {χ ψ : order88_C8 →* Multiplicative (ZMod 2)}
    (hgen : χ (Multiplicative.ofAdd (1 : ZMod 8)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 8))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 8 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 8)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 8)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 8)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 8)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

/-- The unique non-trivial `C₈ → C₂` character, up to automorphism of `C₈`. -/
noncomputable abbrev order88_chiC8 : order88_C8 →* Multiplicative (ZMod 2) :=
  zmodCastMulHom (by norm_num : 2 ∣ 8)

/-- A character `C₈ → C₂` is trivial or the standard quotient map. -/
theorem order88_c8_character_cases (χ : order88_C8 →* Multiplicative (ZMod 2)) :
    χ = 1 ∨ χ = order88_chiC8 := by
  rcases order88_c2_element_cases (χ (Multiplicative.ofAdd (1 : ZMod 8))) with hgen | hgen
  · left
    apply order88_c8_hom_ext
    simp [hgen]
  · right
    apply order88_c8_hom_ext
    rw [hgen]
    rfl

/-- The `C₄ × C₂ → C₂` character non-trivial on the `C₄` factor. -/
noncomputable abbrev order88_chiC4C2_fst : order88_C4C2 →* Multiplicative (ZMod 2) :=
  (zmodCastMulHom (by norm_num : 2 ∣ 4)).comp
    (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)))

/-- The `C₄ × C₂ → C₂` character non-trivial on the `C₂` factor. -/
noncomputable abbrev order88_chiC4C2_snd : order88_C4C2 →* Multiplicative (ZMod 2) :=
  MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))

/-- The product of the two non-trivial coordinate characters on `C₄ × C₂`. -/
noncomputable abbrev order88_chiC4C2_prod : order88_C4C2 →* Multiplicative (ZMod 2) :=
  order88_chiC4C2_fst * order88_chiC4C2_snd

/-- Characters `C₄ × C₂ → C₂` are determined by the two standard generators. -/
theorem order88_c4c2_hom_ext {χ ψ : order88_C4C2 →* Multiplicative (ZMod 2)}
    (h4 : χ (Multiplicative.ofAdd (1 : ZMod 4), 1) =
      ψ (Multiplicative.ofAdd (1 : ZMod 4), 1))
    (h2 : χ (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      ψ (1, Multiplicative.ofAdd (1 : ZMod 2))) :
    χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨x4, x2⟩
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x4
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective x2
  let g4 : order88_C4C2 := (Multiplicative.ofAdd (1 : ZMod 4), 1)
  let g2 : order88_C4C2 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  have ha : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 4)) ^ a.val := by
    calc
      Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 4)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (a.val • (1 : ZMod 4)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 4)) ^ a.val := by rw [ofAdd_nsmul]
  have hb : Multiplicative.ofAdd b = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by
    calc
      Multiplicative.ofAdd b = Multiplicative.ofAdd ((b.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (b.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by rw [ofAdd_nsmul]
  have hx : (Multiplicative.ofAdd a, Multiplicative.ofAdd b) = g4 ^ a.val * g2 ^ b.val := by
    simp [g4, g2, Prod.pow_mk, ha, hb]
  rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h4, h2]

/-- A character `C₄ × C₂ → C₂` is one of the four coordinate characters. -/
theorem order88_c4c2_character_cases (χ : order88_C4C2 →* Multiplicative (ZMod 2)) :
    χ = 1 ∨ χ = order88_chiC4C2_fst ∨ χ = order88_chiC4C2_snd ∨
      χ = order88_chiC4C2_prod := by
  let g4 : order88_C4C2 := (Multiplicative.ofAdd (1 : ZMod 4), 1)
  let g2 : order88_C4C2 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  rcases order88_c2_element_cases (χ g4) with h4 | h4 <;>
    rcases order88_c2_element_cases (χ g2) with h2 | h2
  · left
    apply order88_c4c2_hom_ext <;> simp [g4, g2, h4, h2]
  · right
    right
    left
    apply order88_c4c2_hom_ext <;> simp [g4, g2, h4, h2, order88_chiC4C2_snd]
  · right
    left
    apply order88_c4c2_hom_ext <;> simp [g4, g2, h4, h2, order88_chiC4C2_fst,
      zmodCastMulHom]
  · right
    right
    right
    apply order88_c4c2_hom_ext <;> simp [g4, g2, h4, h2, order88_chiC4C2_prod,
      order88_chiC4C2_fst, order88_chiC4C2_snd, zmodCastMulHom]

/-- The shear automorphism of `C₄ × C₂` sending the second factor by the first character. -/
noncomputable def order88_C4C2_shear : order88_C4C2 ≃* order88_C4C2 where
  toFun x := (x.1, order88_chiC4C2_fst x * x.2)
  invFun x := (x.1, order88_chiC4C2_fst x * x.2)
  left_inv := by
    intro x
    ext
    · rfl
    · change order88_chiC4C2_fst x * (order88_chiC4C2_fst x * x.2) = x.2
      have hsquare := order88_c2_mul_self (order88_chiC4C2_fst x)
      rw [← mul_assoc, hsquare, one_mul]
  right_inv := by
    intro x
    ext
    · rfl
    · change order88_chiC4C2_fst x * (order88_chiC4C2_fst x * x.2) = x.2
      have hsquare := order88_c2_mul_self (order88_chiC4C2_fst x)
      rw [← mul_assoc, hsquare, one_mul]
  map_mul' := by
    intro x y
    ext
    · rfl
    · change order88_chiC4C2_fst (x * y) * (x.2 * y.2) =
        (order88_chiC4C2_fst x * x.2) * (order88_chiC4C2_fst y * y.2)
      rw [map_mul]
      ac_rfl

/-- The product character lies in the same automorphism orbit as the second projection. -/
theorem order88_chiC4C2_snd_comp_shear :
    order88_chiC4C2_snd.comp order88_C4C2_shear.toMonoidHom =
      order88_chiC4C2_prod := by
  apply order88_c4c2_hom_ext <;> rfl

/-- A representative non-trivial `C₂³ → C₂` character. -/
noncomputable abbrev order88_chiC2C2C2 : order88_C2C2C2 →* Multiplicative (ZMod 2) :=
  MonoidHom.fst (Multiplicative (ZMod 2))
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

/-- The second-coordinate character on `C₂³`. -/
noncomputable abbrev order88_chiC2C2C2_snd : order88_C2C2C2 →* Multiplicative (ZMod 2) :=
  (MonoidHom.fst (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2))).comp
    (MonoidHom.snd (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))

/-- The third-coordinate character on `C₂³`. -/
noncomputable abbrev order88_chiC2C2C2_trd : order88_C2C2C2 →* Multiplicative (ZMod 2) :=
  (MonoidHom.snd (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2))).comp
    (MonoidHom.snd (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))

/-- The product of the first two coordinate characters on `C₂³`. -/
noncomputable abbrev order88_chiC2C2C2_fst_snd :
    order88_C2C2C2 →* Multiplicative (ZMod 2) :=
  order88_chiC2C2C2 * order88_chiC2C2C2_snd

/-- The product of the first and third coordinate characters on `C₂³`. -/
noncomputable abbrev order88_chiC2C2C2_fst_trd :
    order88_C2C2C2 →* Multiplicative (ZMod 2) :=
  order88_chiC2C2C2 * order88_chiC2C2C2_trd

/-- The product of the last two coordinate characters on `C₂³`. -/
noncomputable abbrev order88_chiC2C2C2_snd_trd :
    order88_C2C2C2 →* Multiplicative (ZMod 2) :=
  order88_chiC2C2C2_snd * order88_chiC2C2C2_trd

/-- The product of all three coordinate characters on `C₂³`. -/
noncomputable abbrev order88_chiC2C2C2_fst_snd_trd :
    order88_C2C2C2 →* Multiplicative (ZMod 2) :=
  order88_chiC2C2C2 * order88_chiC2C2C2_snd * order88_chiC2C2C2_trd

/-- Characters `C₂³ → C₂` are determined by the three standard generators. -/
theorem order88_c2c2c2_hom_ext {χ ψ : order88_C2C2C2 →* Multiplicative (ZMod 2)}
    (h1 : χ (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      ψ (Multiplicative.ofAdd (1 : ZMod 2), 1))
    (h2 : χ (1, (Multiplicative.ofAdd (1 : ZMod 2), 1)) =
      ψ (1, (Multiplicative.ofAdd (1 : ZMod 2), 1)))
    (h3 : χ (1, (1, Multiplicative.ofAdd (1 : ZMod 2))) =
      ψ (1, (1, Multiplicative.ofAdd (1 : ZMod 2)))) :
    χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨x1, x23⟩
  rcases x23 with ⟨x2, x3⟩
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x1
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective x2
  obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective x3
  let g1 : order88_C2C2C2 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order88_C2C2C2 := (1, (Multiplicative.ofAdd (1 : ZMod 2), 1))
  let g3 : order88_C2C2C2 := (1, (1, Multiplicative.ofAdd (1 : ZMod 2)))
  have ha : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by
    calc
      Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (a.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by rw [ofAdd_nsmul]
  have hb : Multiplicative.ofAdd b = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by
    calc
      Multiplicative.ofAdd b = Multiplicative.ofAdd ((b.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (b.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by rw [ofAdd_nsmul]
  have hc : Multiplicative.ofAdd c = (Multiplicative.ofAdd (1 : ZMod 2)) ^ c.val := by
    calc
      Multiplicative.ofAdd c = Multiplicative.ofAdd ((c.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (c.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ c.val := by rw [ofAdd_nsmul]
  have hx : (Multiplicative.ofAdd a, (Multiplicative.ofAdd b, Multiplicative.ofAdd c)) =
      g1 ^ a.val * g2 ^ b.val * g3 ^ c.val := by
    simp [g1, g2, g3, Prod.pow_mk, ha, hb, hc]
  rw [hx, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_pow, map_pow, h1, h2, h3]

/-- A character `C₂³ → C₂` is one of the eight coordinate products. -/
theorem order88_c2c2c2_character_cases (χ : order88_C2C2C2 →* Multiplicative (ZMod 2)) :
    χ = 1 ∨ χ = order88_chiC2C2C2 ∨ χ = order88_chiC2C2C2_snd ∨
      χ = order88_chiC2C2C2_trd ∨ χ = order88_chiC2C2C2_fst_snd ∨
      χ = order88_chiC2C2C2_fst_trd ∨ χ = order88_chiC2C2C2_snd_trd ∨
      χ = order88_chiC2C2C2_fst_snd_trd := by
  let g1 : order88_C2C2C2 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order88_C2C2C2 := (1, (Multiplicative.ofAdd (1 : ZMod 2), 1))
  let g3 : order88_C2C2C2 := (1, (1, Multiplicative.ofAdd (1 : ZMod 2)))
  rcases order88_c2_element_cases (χ g1) with h1 | h1 <;>
    rcases order88_c2_element_cases (χ g2) with h2 | h2 <;>
      rcases order88_c2_element_cases (χ g3) with h3 | h3
  · left
    apply order88_c2c2c2_hom_ext <;> simp [g1, g2, g3, h1, h2, h3]
  · right
    right
    right
    left
    apply order88_c2c2c2_hom_ext <;> simp [g1, g2, g3, h1, h2, h3,
      order88_chiC2C2C2_trd]
  · right
    right
    left
    apply order88_c2c2c2_hom_ext <;> simp [g1, g2, g3, h1, h2, h3,
      order88_chiC2C2C2_snd]
  · right
    right
    right
    right
    right
    right
    left
    apply order88_c2c2c2_hom_ext <;> simp [g1, g2, g3, h1, h2, h3,
      order88_chiC2C2C2_snd_trd, order88_chiC2C2C2_snd, order88_chiC2C2C2_trd]
  · right
    left
    apply order88_c2c2c2_hom_ext <;> simp [g1, g2, g3, h1, h2, h3,
      order88_chiC2C2C2]
  · right
    right
    right
    right
    right
    left
    apply order88_c2c2c2_hom_ext <;> simp [g1, g2, g3, h1, h2, h3,
      order88_chiC2C2C2_fst_trd, order88_chiC2C2C2, order88_chiC2C2C2_trd]
  · right
    right
    right
    right
    left
    apply order88_c2c2c2_hom_ext <;> simp [g1, g2, g3, h1, h2, h3,
      order88_chiC2C2C2_fst_snd, order88_chiC2C2C2, order88_chiC2C2C2_snd]
  · right
    right
    right
    right
    right
    right
    right
    apply order88_c2c2c2_hom_ext <;> simp [g1, g2, g3, h1, h2, h3,
      order88_chiC2C2C2_fst_snd_trd, order88_chiC2C2C2, order88_chiC2C2C2_snd,
      order88_chiC2C2C2_trd]

/-- Swap the first and second coordinates of `C₂³`. -/
noncomputable def order88_C2C2C2_swap12 : order88_C2C2C2 ≃* order88_C2C2C2 where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  right_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> decide

/-- Swap the first and third coordinates of `C₂³`. -/
noncomputable def order88_C2C2C2_swap13 : order88_C2C2C2 ≃* order88_C2C2C2 where
  toFun x := (x.2.2, (x.2.1, x.1))
  invFun x := (x.2.2, (x.2.1, x.1))
  left_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  right_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> decide

/-- Add the second coordinate to the first coordinate of `C₂³`. -/
noncomputable def order88_C2C2C2_shear12 : order88_C2C2C2 ≃* order88_C2C2C2 where
  toFun x := (x.1 * x.2.1, (x.2.1, x.2.2))
  invFun x := (x.1 * x.2.1, (x.2.1, x.2.2))
  left_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  right_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> decide

/-- Add the third coordinate to the first coordinate of `C₂³`. -/
noncomputable def order88_C2C2C2_shear13 : order88_C2C2C2 ≃* order88_C2C2C2 where
  toFun x := (x.1 * x.2.2, (x.2.1, x.2.2))
  invFun x := (x.1 * x.2.2, (x.2.1, x.2.2))
  left_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  right_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> decide

/-- Put the product of the second and third coordinates in the first coordinate of `C₂³`. -/
noncomputable def order88_C2C2C2_shear23 : order88_C2C2C2 ≃* order88_C2C2C2 where
  toFun x := (x.2.1 * x.2.2, (x.2.1, x.1))
  invFun x := (x.2.2, (x.2.1, x.1 * x.2.1))
  left_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  right_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> decide

/-- Put the product of all three coordinates in the first coordinate of `C₂³`. -/
noncomputable def order88_C2C2C2_shear123 : order88_C2C2C2 ≃* order88_C2C2C2 where
  toFun x := (x.1 * x.2.1 * x.2.2, (x.2.1, x.2.2))
  invFun x := (x.1 * x.2.1 * x.2.2, (x.2.1, x.2.2))
  left_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  right_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> decide

/-- The second-coordinate character lies in the orbit of the first-coordinate character. -/
theorem order88_chiC2C2C2_comp_swap12 :
    order88_chiC2C2C2.comp order88_C2C2C2_swap12.toMonoidHom =
      order88_chiC2C2C2_snd := by
  apply order88_c2c2c2_hom_ext <;> rfl

/-- The third-coordinate character lies in the orbit of the first-coordinate character. -/
theorem order88_chiC2C2C2_comp_swap13 :
    order88_chiC2C2C2.comp order88_C2C2C2_swap13.toMonoidHom =
      order88_chiC2C2C2_trd := by
  apply order88_c2c2c2_hom_ext <;> rfl

/-- The first-second product character lies in the orbit of the first-coordinate character. -/
theorem order88_chiC2C2C2_comp_shear12 :
    order88_chiC2C2C2.comp order88_C2C2C2_shear12.toMonoidHom =
      order88_chiC2C2C2_fst_snd := by
  apply order88_c2c2c2_hom_ext <;> rfl

/-- The first-third product character lies in the orbit of the first-coordinate character. -/
theorem order88_chiC2C2C2_comp_shear13 :
    order88_chiC2C2C2.comp order88_C2C2C2_shear13.toMonoidHom =
      order88_chiC2C2C2_fst_trd := by
  apply order88_c2c2c2_hom_ext <;> rfl

/-- The second-third product character lies in the orbit of the first-coordinate character. -/
theorem order88_chiC2C2C2_comp_shear23 :
    order88_chiC2C2C2.comp order88_C2C2C2_shear23.toMonoidHom =
      order88_chiC2C2C2_snd_trd := by
  apply order88_c2c2c2_hom_ext <;> rfl

/-- The product of all three characters lies in the orbit of the first-coordinate character. -/
theorem order88_chiC2C2C2_comp_shear123 :
    order88_chiC2C2C2.comp order88_C2C2C2_shear123.toMonoidHom =
      order88_chiC2C2C2_fst_snd_trd := by
  apply order88_c2c2c2_hom_ext <;> rfl

/-- The `D₈ → C₂` character non-trivial on rotations. -/
noncomputable def order88_chiD8_rot : order88_D8 →* Multiplicative (ZMod 2) where
  toFun
    | DihedralGroup.r i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 4)
        (ZMod 2)) i)
    | DihedralGroup.sr i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 4)
        (ZMod 2)) i)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · simp [DihedralGroup.r_mul_r, map_add, ofAdd_add]
    · simp only [DihedralGroup.r_mul_sr]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl
    · simp [DihedralGroup.sr_mul_r, map_add, ofAdd_add]
    · simp only [DihedralGroup.sr_mul_sr]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl

/-- The `D₈ → C₂` character non-trivial on reflections. -/
noncomputable def order88_chiD8_ref : order88_D8 →* Multiplicative (ZMod 2) where
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => Multiplicative.ofAdd (1 : ZMod 2)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · rfl
    · rfl
    · simp only [DihedralGroup.sr_mul_sr]
      decide

/-- The product of the rotation and reflection characters on `D₈`. -/
noncomputable abbrev order88_chiD8_prod : order88_D8 →* Multiplicative (ZMod 2) :=
  order88_chiD8_rot * order88_chiD8_ref

/-- Characters `D₈ → C₂` are determined by `r 1` and `sr 0`. -/
theorem order88_d8_hom_ext {χ ψ : order88_D8 →* Multiplicative (ZMod 2)}
    (hr : χ (DihedralGroup.r (1 : ZMod 4)) = ψ (DihedralGroup.r (1 : ZMod 4)))
    (hs : χ (DihedralGroup.sr (0 : ZMod 4)) = ψ (DihedralGroup.sr (0 : ZMod 4))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases x with i | i
  · have hi : DihedralGroup.r i = (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by
      calc
        DihedralGroup.r i = DihedralGroup.r ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = DihedralGroup.r ((1 : ZMod 4) * (i.val : ZMod 4)) := by simp
        _ = (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by rw [DihedralGroup.r_pow]
    rw [hi, map_pow, map_pow, hr]
  · have hri : DihedralGroup.r i = (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by
      calc
        DihedralGroup.r i = DihedralGroup.r ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = DihedralGroup.r ((1 : ZMod 4) * (i.val : ZMod 4)) := by simp
        _ = (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by rw [DihedralGroup.r_pow]
    have hi : DihedralGroup.sr i =
        DihedralGroup.sr (0 : ZMod 4) * (DihedralGroup.r (1 : ZMod 4)) ^ i.val := by
      rw [← hri]
      simp [DihedralGroup.sr_mul_r]
    rw [hi, map_mul, map_mul, map_pow, map_pow, hs, hr]

/-- A character `D₈ → C₂` is one of the four rotation/reflection characters. -/
theorem order88_d8_character_cases (χ : order88_D8 →* Multiplicative (ZMod 2)) :
    χ = 1 ∨ χ = order88_chiD8_rot ∨ χ = order88_chiD8_ref ∨
      χ = order88_chiD8_prod := by
  let r1 : order88_D8 := DihedralGroup.r (1 : ZMod 4)
  let s0 : order88_D8 := DihedralGroup.sr (0 : ZMod 4)
  rcases order88_c2_element_cases (χ r1) with hr | hr <;>
    rcases order88_c2_element_cases (χ s0) with hs | hs
  · left
    apply order88_d8_hom_ext <;> simp [r1, s0, hr, hs]
  · right
    right
    left
    apply order88_d8_hom_ext <;> simp [r1, s0, hr, hs, order88_chiD8_ref] <;> rfl
  · right
    left
    apply order88_d8_hom_ext <;> simp [r1, s0, hr, hs, order88_chiD8_rot]
  · right
    right
    right
    apply order88_d8_hom_ext <;> simp [r1, s0, hr, hs, order88_chiD8_prod,
      order88_chiD8_rot, order88_chiD8_ref] <;> rfl

/-- The automorphism of `D₈` fixing rotations and shifting reflections. -/
noncomputable def order88_D8_shear : order88_D8 ≃* order88_D8 where
  toFun
    | DihedralGroup.r i => DihedralGroup.r i
    | DihedralGroup.sr i => DihedralGroup.sr (i + 1)
  invFun
    | DihedralGroup.r i => DihedralGroup.r i
    | DihedralGroup.sr i => DihedralGroup.sr (i - 1)
  left_inv := by
    rintro (i | i) <;> simp
  right_inv := by
    rintro (i | i) <;> simp
  map_mul' := by
    rintro (i | i) (j | j) <;> simp [add_assoc, sub_eq_add_neg]
    · ring_nf
    · ring_nf

/-- The product character lies in the same automorphism orbit as the rotation character. -/
theorem order88_chiD8_rot_comp_shear :
    order88_chiD8_rot.comp order88_D8_shear.toMonoidHom = order88_chiD8_prod := by
  apply order88_d8_hom_ext <;> rfl

/-- A representative non-trivial `Q₈ → C₂` character. -/
noncomputable def order88_chiQ8 : order88_Q8 →* Multiplicative (ZMod 2) where
  toFun
    | QuaternionGroup.a i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 4)
        (ZMod 2)) i)
    | QuaternionGroup.xa i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 4)
        (ZMod 2)) i)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · simp [QuaternionGroup.a_mul_a, map_add, ofAdd_add]
    · simp only [QuaternionGroup.a_mul_xa]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl
    · simp [QuaternionGroup.xa_mul_a, map_add, ofAdd_add]
    · simp only [QuaternionGroup.xa_mul_xa]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl

/-- The `Q₈ → C₂` character non-trivial on `xa 0`. -/
noncomputable def order88_chiQ8_xa : order88_Q8 →* Multiplicative (ZMod 2) where
  toFun
    | QuaternionGroup.a _ => 1
    | QuaternionGroup.xa _ => Multiplicative.ofAdd (1 : ZMod 2)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · rfl
    · rfl
    · simp only [QuaternionGroup.xa_mul_xa]
      decide

/-- The product of the two displayed `Q₈ → C₂` characters. -/
noncomputable abbrev order88_chiQ8_prod : order88_Q8 →* Multiplicative (ZMod 2) :=
  order88_chiQ8 * order88_chiQ8_xa

/-- Characters `Q₈ → C₂` are determined by `a 1` and `xa 0`. -/
theorem order88_q8_hom_ext {χ ψ : order88_Q8 →* Multiplicative (ZMod 2)}
    (ha : χ (QuaternionGroup.a (1 : ZMod 4)) = ψ (QuaternionGroup.a (1 : ZMod 4)))
    (hx : χ (QuaternionGroup.xa (0 : ZMod 4)) = ψ (QuaternionGroup.xa (0 : ZMod 4))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases x with i | i
  · have hi : QuaternionGroup.a i = (QuaternionGroup.a (1 : ZMod 4) : order88_Q8) ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = (QuaternionGroup.a (1 : ZMod 4) : order88_Q8) ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    rw [hi, map_pow, map_pow, ha]
  · have hai : QuaternionGroup.a i = (QuaternionGroup.a (1 : ZMod 4) : order88_Q8) ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = (QuaternionGroup.a (1 : ZMod 4) : order88_Q8) ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    have hi : QuaternionGroup.xa i =
        QuaternionGroup.xa (0 : ZMod 4) *
          (QuaternionGroup.a (1 : ZMod 4) : order88_Q8) ^ i.val := by
      rw [← hai]
      simp [QuaternionGroup.xa_mul_a]
    rw [hi, map_mul, map_mul, map_pow, map_pow, hx, ha]

/-- A character `Q₈ → C₂` is one of the four displayed characters. -/
theorem order88_q8_character_cases (χ : order88_Q8 →* Multiplicative (ZMod 2)) :
    χ = 1 ∨ χ = order88_chiQ8 ∨ χ = order88_chiQ8_xa ∨
      χ = order88_chiQ8_prod := by
  let a1 : order88_Q8 := QuaternionGroup.a (1 : ZMod 4)
  let x0 : order88_Q8 := QuaternionGroup.xa (0 : ZMod 4)
  rcases order88_c2_element_cases (χ a1) with ha | ha <;>
    rcases order88_c2_element_cases (χ x0) with hx | hx
  · left
    apply order88_q8_hom_ext <;> simp [a1, x0, ha, hx]
  · right
    right
    left
    apply order88_q8_hom_ext <;> simp [a1, x0, ha, hx, order88_chiQ8_xa] <;> rfl
  · right
    left
    apply order88_q8_hom_ext <;> simp [a1, x0, ha, hx, order88_chiQ8]
  · right
    right
    right
    apply order88_q8_hom_ext <;> simp [a1, x0, ha, hx, order88_chiQ8_prod,
      order88_chiQ8, order88_chiQ8_xa] <;> rfl

/-- The automorphism of `Q₈` fixing `a` and shifting the `xa` coset. -/
noncomputable def order88_Q8_shear : order88_Q8 ≃* order88_Q8 where
  toFun
    | QuaternionGroup.a i => QuaternionGroup.a i
    | QuaternionGroup.xa i => QuaternionGroup.xa (i + 1)
  invFun
    | QuaternionGroup.a i => QuaternionGroup.a i
    | QuaternionGroup.xa i => QuaternionGroup.xa (i - 1)
  left_inv := by
    rintro (i | i) <;> simp
  right_inv := by
    rintro (i | i) <;> simp
  map_mul' := by
    rintro (i | i) (j | j) <;> simp [add_assoc, sub_eq_add_neg]
    · ring_nf
    · ring_nf

/-- The product character lies in the same automorphism orbit as `order88_chiQ8`. -/
theorem order88_chiQ8_comp_shear :
    order88_chiQ8.comp order88_Q8_shear.toMonoidHom = order88_chiQ8_prod := by
  apply order88_q8_hom_ext <;> rfl

/-- The automorphism of `Q₈` exchanging the displayed four-order generators. -/
noncomputable def order88_Q8_swap : order88_Q8 ≃* order88_Q8 where
  toFun
    | QuaternionGroup.a i => (QuaternionGroup.xa (0 : ZMod 4) : order88_Q8) ^ i.val
    | QuaternionGroup.xa i => (QuaternionGroup.a (1 : ZMod 4) : order88_Q8) *
        (QuaternionGroup.xa (0 : ZMod 4) : order88_Q8) ^ i.val
  invFun
    | QuaternionGroup.a i => (QuaternionGroup.xa (0 : ZMod 4) : order88_Q8) ^ i.val
    | QuaternionGroup.xa i => (QuaternionGroup.a (1 : ZMod 4) : order88_Q8) *
        (QuaternionGroup.xa (0 : ZMod 4) : order88_Q8) ^ i.val
  left_inv := by
    rintro (i | i) <;> fin_cases i <;> decide
  right_inv := by
    rintro (i | i) <;> fin_cases i <;> decide
  map_mul' := by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> decide

/-- The `xa` character lies in the same automorphism orbit as `order88_chiQ8`. -/
theorem order88_chiQ8_comp_swap :
    order88_chiQ8.comp order88_Q8_swap.toMonoidHom = order88_chiQ8_xa := by
  apply order88_q8_hom_ext <;> rfl

/-- Turn a character `H → C₂` into the corresponding inversion action on `C₁₁`. -/
noncomputable abbrev order88_action {H : Type} [Group H]
    (χ : H →* Multiplicative (ZMod 2)) : H →* MulAut order88_C11 :=
  (invActionHom order88_C11).comp χ

/-- Precomposing a character by an automorphism precomposes the corresponding action. -/
theorem order88_action_comp {H : Type} [Group H] {χ ψ : H →* Multiplicative (ZMod 2)}
    (σ : H ≃* H) (hχ : χ.comp σ.toMonoidHom = ψ) :
    (order88_action χ).comp σ.toMonoidHom = order88_action ψ := by
  ext h x
  change (invActionHom order88_C11) (χ (σ h)) x = (invActionHom order88_C11) (ψ h) x
  rw [show χ (σ h) = ψ h from congrArg (fun f : H →* Multiplicative (ZMod 2) => f h) hχ]

/-- Every action `H → Aut(C₁₁)` with `|H| = 8` is induced by its character `H → C₂`. -/
theorem order88_action_eq_actionCharacter {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 8) (φ : H →* MulAut order88_C11) :
    φ = order88_action (order88_actionCharacter hH φ) := by
  ext h x
  rcases order88_action_value_eq_one_or_inv hH φ h with hh | hh
  · have hchi : order88_actionCharacter hH φ h = 1 := by
      classical
      simp [order88_actionCharacter, hh]
    simp [order88_action, hchi, hh]
  · have hchi : order88_actionCharacter hH φ h = Multiplicative.ofAdd (1 : ZMod 2) := by
      classical
      simp [order88_actionCharacter, hh, order88_invAut_ne_one]
    simp [order88_action, hchi, hh, invActionHom_gen]

/-- An action `C₈ → Aut(C₁₁)` is trivial or the standard inversion action. -/
theorem order88_c8_action_cases (φ : order88_C8 →* MulAut order88_C11) :
    φ = 1 ∨ φ = order88_action order88_chiC8 := by
  have hcard : Nat.card order88_C8 = 8 := card_cyclicRep (by norm_num)
  have hφ := order88_action_eq_actionCharacter hcard φ
  rcases order88_c8_character_cases (order88_actionCharacter hcard φ) with hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right
    rw [hφ, hχ]

/-- An action `C₄ × C₂ → Aut(C₁₁)` is induced by one of the four characters. -/
theorem order88_c4c2_action_cases (φ : order88_C4C2 →* MulAut order88_C11) :
    φ = 1 ∨ φ = order88_action order88_chiC4C2_fst ∨
      φ = order88_action order88_chiC4C2_snd ∨
      φ = order88_action order88_chiC4C2_prod := by
  have hcard : Nat.card order88_C4C2 = 8 := by
    rw [Nat.card_prod, card_cyclicRep (by norm_num : 4 ≠ 0),
      card_cyclicRep (by norm_num : 2 ≠ 0)]
  have hφ := order88_action_eq_actionCharacter hcard φ
  rcases order88_c4c2_character_cases (order88_actionCharacter hcard φ) with
    hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right
    left
    rw [hφ, hχ]
  · right
    right
    left
    rw [hφ, hχ]
  · right
    right
    right
    rw [hφ, hχ]

/-- An action `C₂³ → Aut(C₁₁)` is induced by one of the eight characters. -/
theorem order88_c2c2c2_action_cases (φ : order88_C2C2C2 →* MulAut order88_C11) :
    φ = 1 ∨ φ = order88_action order88_chiC2C2C2 ∨
      φ = order88_action order88_chiC2C2C2_snd ∨
      φ = order88_action order88_chiC2C2C2_trd ∨
      φ = order88_action order88_chiC2C2C2_fst_snd ∨
      φ = order88_action order88_chiC2C2C2_fst_trd ∨
      φ = order88_action order88_chiC2C2C2_snd_trd ∨
      φ = order88_action order88_chiC2C2C2_fst_snd_trd := by
  have hcard : Nat.card order88_C2C2C2 = 8 := by
    rw [Nat.card_prod, Nat.card_prod]
    norm_num [card_cyclicRep (by norm_num : 2 ≠ 0)]
  have hφ := order88_action_eq_actionCharacter hcard φ
  rcases order88_c2c2c2_character_cases (order88_actionCharacter hcard φ) with
    hχ | hχ | hχ | hχ | hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right
    left
    rw [hφ, hχ]
  · right
    right
    left
    rw [hφ, hχ]
  · right
    right
    right
    left
    rw [hφ, hχ]
  · right
    right
    right
    right
    left
    rw [hφ, hχ]
  · right
    right
    right
    right
    right
    left
    rw [hφ, hχ]
  · right
    right
    right
    right
    right
    right
    left
    rw [hφ, hχ]
  · right
    right
    right
    right
    right
    right
    right
    rw [hφ, hχ]

/-- An action `D₈ → Aut(C₁₁)` is induced by one of the four characters. -/
theorem order88_d8_action_cases (φ : order88_D8 →* MulAut order88_C11) :
    φ = 1 ∨ φ = order88_action order88_chiD8_rot ∨
      φ = order88_action order88_chiD8_ref ∨
      φ = order88_action order88_chiD8_prod := by
  have hcard : Nat.card order88_D8 = 8 := by
    rw [DihedralGroup.nat_card]
  have hφ := order88_action_eq_actionCharacter hcard φ
  rcases order88_d8_character_cases (order88_actionCharacter hcard φ) with hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right
    left
    rw [hφ, hχ]
  · right
    right
    left
    rw [hφ, hχ]
  · right
    right
    right
    rw [hφ, hχ]

/-- An action `Q₈ → Aut(C₁₁)` is induced by one of the four characters. -/
theorem order88_q8_action_cases (φ : order88_Q8 →* MulAut order88_C11) :
    φ = 1 ∨ φ = order88_action order88_chiQ8 ∨
      φ = order88_action order88_chiQ8_xa ∨
      φ = order88_action order88_chiQ8_prod := by
  have hcard : Nat.card order88_Q8 = 8 := by
    rw [P3Group.card_quaternion8]
    norm_num
  have hφ := order88_action_eq_actionCharacter hcard φ
  rcases order88_q8_character_cases (order88_actionCharacter hcard φ) with hχ | hχ | hχ | hχ
  · left
    rw [hφ, hχ]
    rfl
  · right
    left
    rw [hφ, hχ]
  · right
    right
    left
    rw [hφ, hχ]
  · right
    right
    right
    rw [hφ, hχ]

/-- Semidirect-product representative attached to a character `χ : H → C₂`. -/
noncomputable abbrev order88_SD (H : Type) [Group H] (χ : H →* Multiplicative (ZMod 2)) :
    Type :=
  SemidirectProduct order88_C11 H (order88_action χ)

noncomputable instance instFintypeOrder88SD {H : Type} [Group H] [Fintype H]
    (χ : H →* Multiplicative (ZMod 2)) : Fintype (order88_SD H χ) :=
  Fintype.ofEquiv (order88_C11 × H) SemidirectProduct.equivProd.symm

/-- Precomposing a character by an automorphism gives an isomorphic semidirect product. -/
noncomputable def order88_SD_equiv_of_character_comp {H : Type} [Group H]
    (χ ψ : H →* Multiplicative (ZMod 2)) (σ : H ≃* H)
    (hχ : χ.comp σ.toMonoidHom = ψ) :
    order88_SD H ψ ≃* order88_SD H χ := by
  have haction :
      (order88_action χ).comp σ.toMonoidHom = order88_action ψ :=
    order88_action_comp σ hχ
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order88_C11) (φ := order88_action χ) σ)

/-- The extra `C₄ × C₂` product-character semidirect product is isomorphic to the `snd` case. -/
noncomputable def order88_c4c2_prod_equiv_snd :
    order88_SD order88_C4C2 order88_chiC4C2_prod ≃*
      order88_SD order88_C4C2 order88_chiC4C2_snd := by
  have haction :
      (order88_action order88_chiC4C2_snd).comp order88_C4C2_shear.toMonoidHom =
        order88_action order88_chiC4C2_prod :=
    order88_action_comp order88_C4C2_shear order88_chiC4C2_snd_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order88_C11) (φ := order88_action order88_chiC4C2_snd)
      order88_C4C2_shear)

/-- The extra `D₈` product-character semidirect product is isomorphic to the rotation case. -/
noncomputable def order88_d8_prod_equiv_rot :
    order88_SD order88_D8 order88_chiD8_prod ≃*
      order88_SD order88_D8 order88_chiD8_rot := by
  have haction :
      (order88_action order88_chiD8_rot).comp order88_D8_shear.toMonoidHom =
        order88_action order88_chiD8_prod :=
    order88_action_comp order88_D8_shear order88_chiD8_rot_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order88_C11) (φ := order88_action order88_chiD8_rot)
      order88_D8_shear)

/-- The extra `Q₈` product-character semidirect product is isomorphic to the displayed `Q₈` case. -/
noncomputable def order88_q8_prod_equiv_q8 :
    order88_SD order88_Q8 order88_chiQ8_prod ≃*
      order88_SD order88_Q8 order88_chiQ8 := by
  have haction :
      (order88_action order88_chiQ8).comp order88_Q8_shear.toMonoidHom =
        order88_action order88_chiQ8_prod :=
    order88_action_comp order88_Q8_shear order88_chiQ8_comp_shear
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order88_C11) (φ := order88_action order88_chiQ8)
      order88_Q8_shear)

/-- The extra `Q₈` `xa`-character semidirect product is isomorphic to the displayed `Q₈` case. -/
noncomputable def order88_q8_xa_equiv_q8 :
    order88_SD order88_Q8 order88_chiQ8_xa ≃*
      order88_SD order88_Q8 order88_chiQ8 := by
  have haction :
      (order88_action order88_chiQ8).comp order88_Q8_swap.toMonoidHom =
        order88_action order88_chiQ8_xa :=
    order88_action_comp order88_Q8_swap order88_chiQ8_comp_swap
  exact (semidirectProductCongr_eq haction.symm).trans
    (semidirectProductCongrAut (N := order88_C11) (φ := order88_action order88_chiQ8)
      order88_Q8_swap)

/-- The second-coordinate `C₂³` semidirect product is isomorphic to the first-coordinate case. -/
noncomputable def order88_c2c2c2_snd_equiv :
    order88_SD order88_C2C2C2 order88_chiC2C2C2_snd ≃*
      order88_SD order88_C2C2C2 order88_chiC2C2C2 :=
  order88_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_snd
    order88_C2C2C2_swap12 order88_chiC2C2C2_comp_swap12

/-- The third-coordinate `C₂³` semidirect product is isomorphic to the first-coordinate case. -/
noncomputable def order88_c2c2c2_trd_equiv :
    order88_SD order88_C2C2C2 order88_chiC2C2C2_trd ≃*
      order88_SD order88_C2C2C2 order88_chiC2C2C2 :=
  order88_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_trd
    order88_C2C2C2_swap13 order88_chiC2C2C2_comp_swap13

/-- The `fst*snd` `C₂³` semidirect product is isomorphic to the first-coordinate case. -/
noncomputable def order88_c2c2c2_fst_snd_equiv :
    order88_SD order88_C2C2C2 order88_chiC2C2C2_fst_snd ≃*
      order88_SD order88_C2C2C2 order88_chiC2C2C2 :=
  order88_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_snd
    order88_C2C2C2_shear12 order88_chiC2C2C2_comp_shear12

/-- The `fst*trd` `C₂³` semidirect product is isomorphic to the first-coordinate case. -/
noncomputable def order88_c2c2c2_fst_trd_equiv :
    order88_SD order88_C2C2C2 order88_chiC2C2C2_fst_trd ≃*
      order88_SD order88_C2C2C2 order88_chiC2C2C2 :=
  order88_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_trd
    order88_C2C2C2_shear13 order88_chiC2C2C2_comp_shear13

/-- The `snd*trd` `C₂³` semidirect product is isomorphic to the first-coordinate case. -/
noncomputable def order88_c2c2c2_snd_trd_equiv :
    order88_SD order88_C2C2C2 order88_chiC2C2C2_snd_trd ≃*
      order88_SD order88_C2C2C2 order88_chiC2C2C2 :=
  order88_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_snd_trd
    order88_C2C2C2_shear23 order88_chiC2C2C2_comp_shear23

/-- The `fst*snd*trd` `C₂³` semidirect product is isomorphic to the first-coordinate case. -/
noncomputable def order88_c2c2c2_fst_snd_trd_equiv :
    order88_SD order88_C2C2C2 order88_chiC2C2C2_fst_snd_trd ≃*
      order88_SD order88_C2C2C2 order88_chiC2C2C2 :=
  order88_SD_equiv_of_character_comp order88_chiC2C2C2 order88_chiC2C2C2_fst_snd_trd
    order88_C2C2C2_shear123 order88_chiC2C2C2_comp_shear123

/-- Direct-product representative with complement `H`. -/
abbrev order88_DP (H : Type) : Type := order88_C11 × H

abbrev order88_RA : Type := order88_DP order88_C8
abbrev order88_RB : Type := order88_DP order88_C4C2
abbrev order88_RC : Type := order88_DP order88_C2C2C2
abbrev order88_RD : Type := order88_DP order88_D8
abbrev order88_RE : Type := order88_DP order88_Q8
noncomputable abbrev order88_RF : Type := order88_SD order88_C8 order88_chiC8
noncomputable abbrev order88_RG : Type := order88_SD order88_C4C2 order88_chiC4C2_fst
noncomputable abbrev order88_RH : Type := order88_SD order88_C4C2 order88_chiC4C2_snd
noncomputable abbrev order88_RI : Type := order88_SD order88_C2C2C2 order88_chiC2C2C2
noncomputable abbrev order88_RJ : Type := order88_SD order88_D8 order88_chiD8_rot
noncomputable abbrev order88_RK : Type := order88_SD order88_D8 order88_chiD8_ref
noncomputable abbrev order88_RL : Type := order88_SD order88_Q8 order88_chiQ8

/-- The twelve displayed representatives, indexed for the counting framework. -/
noncomputable abbrev order88_reps : Fin 12 → Type :=
  rep12 order88_RA order88_RB order88_RC order88_RD order88_RE order88_RF
    order88_RG order88_RH order88_RI order88_RJ order88_RK order88_RL

noncomputable instance instGroupOrder88Reps : ∀ i, Group (order88_reps i)
  | 0 => inferInstanceAs (Group order88_RA)
  | 1 => inferInstanceAs (Group order88_RB)
  | 2 => inferInstanceAs (Group order88_RC)
  | 3 => inferInstanceAs (Group order88_RD)
  | 4 => inferInstanceAs (Group order88_RE)
  | 5 => inferInstanceAs (Group order88_RF)
  | 6 => inferInstanceAs (Group order88_RG)
  | 7 => inferInstanceAs (Group order88_RH)
  | 8 => inferInstanceAs (Group order88_RI)
  | 9 => inferInstanceAs (Group order88_RJ)
  | 10 => inferInstanceAs (Group order88_RK)
  | 11 => inferInstanceAs (Group order88_RL)

/-! ### Exhaustiveness -/

/-- The twelve representative cases for groups of order `88`. -/
abbrev order88RepCases (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* order88_RA) ∨ Nonempty (G ≃* order88_RB) ∨
    Nonempty (G ≃* order88_RC) ∨ Nonempty (G ≃* order88_RD) ∨
    Nonempty (G ≃* order88_RE) ∨ Nonempty (G ≃* order88_RF) ∨
    Nonempty (G ≃* order88_RG) ∨ Nonempty (G ≃* order88_RH) ∨
    Nonempty (G ≃* order88_RI) ∨ Nonempty (G ≃* order88_RJ) ∨
    Nonempty (G ≃* order88_RK) ∨ Nonempty (G ≃* order88_RL)

private theorem order88RepCases_ra {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RA)) :
    order88RepCases G := by
  left
  exact h

private theorem order88RepCases_rb {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RB)) :
    order88RepCases G := by
  right
  left
  exact h

private theorem order88RepCases_rc {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RC)) :
    order88RepCases G := by
  right
  right
  left
  exact h

private theorem order88RepCases_rd {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RD)) :
    order88RepCases G := by
  right
  right
  right
  left
  exact h

private theorem order88RepCases_re {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RE)) :
    order88RepCases G := by
  right
  right
  right
  right
  left
  exact h

private theorem order88RepCases_rf {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RF)) :
    order88RepCases G := by
  right
  right
  right
  right
  right
  left
  exact h

private theorem order88RepCases_rg {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RG)) :
    order88RepCases G := by
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order88RepCases_rh {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RH)) :
    order88RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order88RepCases_ri {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RI)) :
    order88RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order88RepCases_rj {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RJ)) :
    order88RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order88RepCases_rk {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RK)) :
    order88RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order88RepCases_rl {G : Type*} [Group G] (h : Nonempty (G ≃* order88_RL)) :
    order88RepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  exact h

private theorem order88_classification_of_c8_action {G : Type*} [Group G]
    {φ : order88_C8 →* MulAut order88_C11}
    (e : G ≃* SemidirectProduct order88_C11 order88_C8 φ) :
    order88RepCases G := by
  rcases order88_c8_action_cases φ with hφ | hφ
  · exact order88RepCases_ra
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩
  · exact order88RepCases_rf ⟨e.trans (semidirectProductCongr_eq hφ)⟩

private theorem order88_classification_of_c4c2_action {G : Type*} [Group G]
    {φ : order88_C4C2 →* MulAut order88_C11}
    (e : G ≃* SemidirectProduct order88_C11 order88_C4C2 φ) :
    order88RepCases G := by
  rcases order88_c4c2_action_cases φ with hφ | hφ | hφ | hφ
  · exact order88RepCases_rb
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩
  · exact order88RepCases_rg ⟨e.trans (semidirectProductCongr_eq hφ)⟩
  · exact order88RepCases_rh ⟨e.trans (semidirectProductCongr_eq hφ)⟩
  · exact order88RepCases_rh
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_c4c2_prod_equiv_snd)⟩

private theorem order88_classification_of_c2c2c2_action {G : Type*} [Group G]
    {φ : order88_C2C2C2 →* MulAut order88_C11}
    (e : G ≃* SemidirectProduct order88_C11 order88_C2C2C2 φ) :
    order88RepCases G := by
  rcases order88_c2c2c2_action_cases φ with
    hφ | hφ | hφ | hφ | hφ | hφ | hφ | hφ
  · exact order88RepCases_rc
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩
  · exact order88RepCases_ri ⟨e.trans (semidirectProductCongr_eq hφ)⟩
  · exact order88RepCases_ri
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_c2c2c2_snd_equiv)⟩
  · exact order88RepCases_ri
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_c2c2c2_trd_equiv)⟩
  · exact order88RepCases_ri
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_c2c2c2_fst_snd_equiv)⟩
  · exact order88RepCases_ri
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_c2c2c2_fst_trd_equiv)⟩
  · exact order88RepCases_ri
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_c2c2c2_snd_trd_equiv)⟩
  · exact order88RepCases_ri
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_c2c2c2_fst_snd_trd_equiv)⟩

private theorem order88_classification_of_d8_action {G : Type*} [Group G]
    {φ : order88_D8 →* MulAut order88_C11}
    (e : G ≃* SemidirectProduct order88_C11 order88_D8 φ) :
    order88RepCases G := by
  rcases order88_d8_action_cases φ with hφ | hφ | hφ | hφ
  · exact order88RepCases_rd
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩
  · exact order88RepCases_rj ⟨e.trans (semidirectProductCongr_eq hφ)⟩
  · exact order88RepCases_rk ⟨e.trans (semidirectProductCongr_eq hφ)⟩
  · exact order88RepCases_rj
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_d8_prod_equiv_rot)⟩

private theorem order88_classification_of_q8_action {G : Type*} [Group G]
    {φ : order88_Q8 →* MulAut order88_C11}
    (e : G ≃* SemidirectProduct order88_C11 order88_Q8 φ) :
    order88RepCases G := by
  rcases order88_q8_action_cases φ with hφ | hφ | hφ | hφ
  · exact order88RepCases_re
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)⟩
  · exact order88RepCases_rl ⟨e.trans (semidirectProductCongr_eq hφ)⟩
  · exact order88RepCases_rl
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_q8_xa_equiv_q8)⟩
  · exact order88RepCases_rl
      ⟨e.trans ((semidirectProductCongr_eq hφ).trans order88_q8_prod_equiv_q8)⟩

/-- Every group of order `88` is isomorphic to one of the twelve displayed representatives. -/
theorem order88_classification [Finite G] (hG : Nat.card G = 88) :
    order88RepCases G := by
  obtain ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩ := order88_semidirectProduct hG
  obtain ⟨eN⟩ := prime_classification (by norm_num : Nat.Prime 11) hcardN
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fintype H := Fintype.ofFinite H
  rcases P3Group.classification 2 H (hcardH.trans (by norm_num)) with
    hH | hH | hH | hH | hH | hH | hH
  · change Nonempty (H ≃* order88_C8) at hH
    obtain ⟨eH⟩ := hH
    exact order88_classification_of_c8_action (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (H ≃* order88_C4C2) at hH
    obtain ⟨eH⟩ := hH
    exact order88_classification_of_c4c2_action (e.trans (SemidirectProduct.congr' eN eH))
  · change Nonempty (H ≃* order88_C2C2C2) at hH
    obtain ⟨eH⟩ := hH
    exact order88_classification_of_c2c2c2_action (e.trans (SemidirectProduct.congr' eN eH))
  · exact (hH.1 rfl).elim
  · exact (hH.1 rfl).elim
  · obtain ⟨eH⟩ := hH.2
    exact order88_classification_of_d8_action (e.trans (SemidirectProduct.congr' eN eH))
  · obtain ⟨eH⟩ := hH.2
    exact order88_classification_of_q8_action (e.trans (SemidirectProduct.congr' eN eH))

/-! ### Cardinalities of the representatives -/



noncomputable def pow_eq_one_card (H : Type*) [Group H] (n : ℕ) : ℕ :=
  Nat.card {x : H // x ^ n = 1}

noncomputable def powEqOneEquivOfMulEquiv {H K : Type*} [Group H] [Group K]
    (n : ℕ) (e : H ≃* K) : {x : H // x ^ n = 1} ≃ {x : K // x ^ n = 1} where
  toFun x := ⟨e x.1, by rw [← map_pow, x.2, map_one]⟩
  invFun x := ⟨e.symm x.1, by
    rw [← map_pow]
    exact e.injective (by simp [x.2])⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

theorem pow_eq_one_card_eq_of_mulEquiv {H K : Type*} [Group H] [Group K]
    (n : ℕ) (e : H ≃* K) :
    pow_eq_one_card H n = pow_eq_one_card K n := by
  exact Nat.card_congr (powEqOneEquivOfMulEquiv n e)

theorem not_nonempty_mulEquiv_of_pow_eq_one_card_ne {H K : Type*} [Group H] [Group K]
    {n : ℕ} (h : pow_eq_one_card H n ≠ pow_eq_one_card K n) :
    ¬ Nonempty (H ≃* K) := by
  rintro ⟨e⟩
  exact h (pow_eq_one_card_eq_of_mulEquiv n e)

theorem card_order88_C11 : Nat.card order88_C11 = 11 := card_cyclicRep (by norm_num)

theorem card_order88_C8 : Nat.card order88_C8 = 8 := card_cyclicRep (by norm_num)

theorem card_order88_C4C2 : Nat.card order88_C4C2 = 8 := by
  rw [Nat.card_prod, card_cyclicRep (by norm_num : 4 ≠ 0),
    card_cyclicRep (by norm_num : 2 ≠ 0)]

theorem card_order88_C2C2C2 : Nat.card order88_C2C2C2 = 8 := by
  rw [Nat.card_prod, Nat.card_prod]
  norm_num [card_cyclicRep (by norm_num : 2 ≠ 0)]

theorem card_order88_D8 : Nat.card order88_D8 = 8 := by
  rw [DihedralGroup.nat_card]

theorem card_order88_Q8 : Nat.card order88_Q8 = 8 := by
  rw [P3Group.card_quaternion8]
  norm_num

theorem card_order88_DP {H : Type} [Group H] (hH : Nat.card H = 8) :
    Nat.card (order88_DP H) = 88 := by
  rw [order88_DP, Nat.card_prod, card_order88_C11, hH]

theorem card_order88_SD {H : Type} [Group H] (χ : H →* Multiplicative (ZMod 2))
    (hH : Nat.card H = 8) : Nat.card (order88_SD H χ) = 88 := by
  rw [order88_SD, SemidirectProduct.card, card_order88_C11, hH]

theorem card_order88_RA : Nat.card order88_RA = 88 := card_order88_DP card_order88_C8
theorem card_order88_RB : Nat.card order88_RB = 88 := card_order88_DP card_order88_C4C2
theorem card_order88_RC : Nat.card order88_RC = 88 := card_order88_DP card_order88_C2C2C2
theorem card_order88_RD : Nat.card order88_RD = 88 := card_order88_DP card_order88_D8
theorem card_order88_RE : Nat.card order88_RE = 88 := card_order88_DP card_order88_Q8
theorem card_order88_RF : Nat.card order88_RF = 88 :=
  card_order88_SD order88_chiC8 card_order88_C8
theorem card_order88_RG : Nat.card order88_RG = 88 :=
  card_order88_SD order88_chiC4C2_fst card_order88_C4C2
theorem card_order88_RH : Nat.card order88_RH = 88 :=
  card_order88_SD order88_chiC4C2_snd card_order88_C4C2
theorem card_order88_RI : Nat.card order88_RI = 88 :=
  card_order88_SD order88_chiC2C2C2 card_order88_C2C2C2
theorem card_order88_RJ : Nat.card order88_RJ = 88 :=
  card_order88_SD order88_chiD8_rot card_order88_D8
theorem card_order88_RK : Nat.card order88_RK = 88 :=
  card_order88_SD order88_chiD8_ref card_order88_D8
theorem card_order88_RL : Nat.card order88_RL = 88 :=
  card_order88_SD order88_chiQ8 card_order88_Q8

/-! ### Center cardinalities of the representatives -/

theorem card_center_order88_RA : Nat.card (Subgroup.center order88_RA) = 88 := by
  rw [card_center_eq_card_of_comm order88_RA (fun a b => mul_comm a b)]
  exact card_order88_RA

theorem card_center_order88_RB : Nat.card (Subgroup.center order88_RB) = 88 := by
  rw [card_center_eq_card_of_comm order88_RB (fun a b => mul_comm a b)]
  exact card_order88_RB

theorem card_center_order88_RC : Nat.card (Subgroup.center order88_RC) = 88 := by
  rw [card_center_eq_card_of_comm order88_RC (fun a b => mul_comm a b)]
  exact card_order88_RC

theorem card_center_order88_D8 : Nat.card (Subgroup.center order88_D8) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact P3Group.center_card_eq_p_of_nonabelian
    (p := 2) (G := order88_D8) (by simpa using P3Group.card_dihedral4)
    P3Group.dihedral4_nonabelian

theorem card_center_order88_Q8 : Nat.card (Subgroup.center order88_Q8) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact P3Group.center_card_eq_p_of_nonabelian
    (p := 2) (G := order88_Q8) (by simpa using P3Group.card_quaternion8)
    P3Group.quaternion8_nonabelian

theorem card_center_order88_RD : Nat.card (Subgroup.center order88_RD) = 22 := by
  change Nat.card (Subgroup.center (order88_C11 × order88_D8)) = 22
  rw [card_center_prod, card_center_eq_card_of_comm order88_C11
    (fun a b => mul_comm a b), card_order88_C11, card_center_order88_D8]

theorem card_center_order88_RE : Nat.card (Subgroup.center order88_RE) = 22 := by
  change Nat.card (Subgroup.center (order88_C11 × order88_Q8)) = 22
  rw [card_center_prod, card_center_eq_card_of_comm order88_C11
    (fun a b => mul_comm a b), card_order88_C11, card_center_order88_Q8]

theorem card_center_order88_RF : Nat.card (Subgroup.center order88_RF) = 4 := by
  have hcard : Fintype.card (Subgroup.center order88_RF) = 4 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_center_order88_RG : Nat.card (Subgroup.center order88_RG) = 4 := by
  have hcard : Fintype.card (Subgroup.center order88_RG) = 4 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_center_order88_RH : Nat.card (Subgroup.center order88_RH) = 4 := by
  have hcard : Fintype.card (Subgroup.center order88_RH) = 4 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_center_order88_RI : Nat.card (Subgroup.center order88_RI) = 4 := by
  have hcard : Fintype.card (Subgroup.center order88_RI) = 4 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_center_order88_RJ : Nat.card (Subgroup.center order88_RJ) = 2 := by
  have hcard : Fintype.card (Subgroup.center order88_RJ) = 2 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_center_order88_RK : Nat.card (Subgroup.center order88_RK) = 2 := by
  have hcard : Fintype.card (Subgroup.center order88_RK) = 2 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_center_order88_RL : Nat.card (Subgroup.center order88_RL) = 2 := by
  have hcard : Fintype.card (Subgroup.center order88_RL) = 2 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

/-- Center cardinalities of the twelve displayed representatives. -/
def order88_center_card : Fin 12 → Nat
  | 0 => 88
  | 1 => 88
  | 2 => 88
  | 3 => 22
  | 4 => 22
  | 5 => 4
  | 6 => 4
  | 7 => 4
  | 8 => 4
  | 9 => 2
  | 10 => 2
  | 11 => 2

theorem card_center_order88_reps (i : Fin 12) :
    Nat.card (Subgroup.center (order88_reps i)) = order88_center_card i := by
  fin_cases i
  · exact card_center_order88_RA
  · exact card_center_order88_RB
  · exact card_center_order88_RC
  · exact card_center_order88_RD
  · exact card_center_order88_RE
  · exact card_center_order88_RF
  · exact card_center_order88_RG
  · exact card_center_order88_RH
  · exact card_center_order88_RI
  · exact card_center_order88_RJ
  · exact card_center_order88_RK
  · exact card_center_order88_RL

theorem not_nonempty_mulEquiv_order88_reps_of_center_card_ne {i j : Fin 12}
    (h : order88_center_card i ≠ order88_center_card j) :
    ¬ Nonempty (order88_reps i ≃* order88_reps j) := by
  exact not_nonempty_mulEquiv_of_card_center_ne (by
    rw [card_center_order88_reps i, card_center_order88_reps j]
    exact h)

theorem card_pow_two_eq_one_order88_RA : pow_eq_one_card order88_RA 2 = 2 := by
  have hcard : Fintype.card {x : order88_RA // x ^ 2 = 1} = 2 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RB : pow_eq_one_card order88_RB 2 = 4 := by
  have hcard : Fintype.card {x : order88_RB // x ^ 2 = 1} = 4 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RC : pow_eq_one_card order88_RC 2 = 8 := by
  have hcard : Fintype.card {x : order88_RC // x ^ 2 = 1} = 8 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RD : pow_eq_one_card order88_RD 2 = 6 := by
  have hcard : Fintype.card {x : order88_RD // x ^ 2 = 1} = 6 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RE : pow_eq_one_card order88_RE 2 = 2 := by
  have hcard : Fintype.card {x : order88_RE // x ^ 2 = 1} = 2 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RF : pow_eq_one_card order88_RF 2 = 2 := by
  have hcard : Fintype.card {x : order88_RF // x ^ 2 = 1} = 2 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RG : pow_eq_one_card order88_RG 2 = 4 := by
  have hcard : Fintype.card {x : order88_RG // x ^ 2 = 1} = 4 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RH : pow_eq_one_card order88_RH 2 = 24 := by
  have hcard : Fintype.card {x : order88_RH // x ^ 2 = 1} = 24 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RI : pow_eq_one_card order88_RI 2 = 48 := by
  have hcard : Fintype.card {x : order88_RI // x ^ 2 = 1} = 48 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RJ : pow_eq_one_card order88_RJ 2 = 26 := by
  have hcard : Fintype.card {x : order88_RJ // x ^ 2 = 1} = 26 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RK : pow_eq_one_card order88_RK 2 = 46 := by
  have hcard : Fintype.card {x : order88_RK // x ^ 2 = 1} = 46 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

theorem card_pow_two_eq_one_order88_RL : pow_eq_one_card order88_RL 2 = 2 := by
  have hcard : Fintype.card {x : order88_RL // x ^ 2 = 1} = 2 := by
    decide +kernel
  exact Nat.card_eq_of_equiv_fin (Fintype.equivFinOfCardEq hcard)

/-- Cardinalities of `{x | x ^ 2 = 1}` in the twelve displayed representatives. -/
def order88_pow_two_eq_one_card : Fin 12 → Nat
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | 3 => 6
  | 4 => 2
  | 5 => 2
  | 6 => 4
  | 7 => 24
  | 8 => 48
  | 9 => 26
  | 10 => 46
  | 11 => 2

theorem card_pow_two_eq_one_order88_reps (i : Fin 12) :
    pow_eq_one_card (order88_reps i) 2 = order88_pow_two_eq_one_card i := by
  fin_cases i
  · exact card_pow_two_eq_one_order88_RA
  · exact card_pow_two_eq_one_order88_RB
  · exact card_pow_two_eq_one_order88_RC
  · exact card_pow_two_eq_one_order88_RD
  · exact card_pow_two_eq_one_order88_RE
  · exact card_pow_two_eq_one_order88_RF
  · exact card_pow_two_eq_one_order88_RG
  · exact card_pow_two_eq_one_order88_RH
  · exact card_pow_two_eq_one_order88_RI
  · exact card_pow_two_eq_one_order88_RJ
  · exact card_pow_two_eq_one_order88_RK
  · exact card_pow_two_eq_one_order88_RL

theorem not_nonempty_mulEquiv_order88_reps_of_pow_two_card_ne {i j : Fin 12}
    (h : order88_pow_two_eq_one_card i ≠ order88_pow_two_eq_one_card j) :
    ¬ Nonempty (order88_reps i ≃* order88_reps j) := by
  exact not_nonempty_mulEquiv_of_pow_eq_one_card_ne (n := 2) (by
    rw [card_pow_two_eq_one_order88_reps i, card_pow_two_eq_one_order88_reps j]
    exact h)

def order88_reps_invariant (i : Fin 12) : Nat × Nat :=
  (order88_center_card i, order88_pow_two_eq_one_card i)

theorem order88_reps_invariant_injective : Function.Injective order88_reps_invariant := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [order88_reps_invariant, order88_center_card, order88_pow_two_eq_one_card] at h ⊢

theorem order88_reps_invariant_eq_of_mulEquiv {i j : Fin 12}
    (hiso : Nonempty (order88_reps i ≃* order88_reps j)) :
    order88_reps_invariant i = order88_reps_invariant j := by
  rcases hiso with ⟨e⟩
  apply Prod.ext
  · change order88_center_card i = order88_center_card j
    rw [← card_center_order88_reps i, ← card_center_order88_reps j]
    exact card_center_eq_of_mulEquiv e
  · change order88_pow_two_eq_one_card i = order88_pow_two_eq_one_card j
    rw [← card_pow_two_eq_one_order88_reps i, ← card_pow_two_eq_one_order88_reps j]
    exact pow_eq_one_card_eq_of_mulEquiv 2 e

theorem order88_reps_pairwise : PairwiseNonMulEquiv order88_reps := by
  intro i j hiso
  exact order88_reps_invariant_injective (order88_reps_invariant_eq_of_mulEquiv hiso)

theorem card_order88_reps (i : Fin 12) : Nat.card (order88_reps i) = 88 := by
  fin_cases i
  · exact card_order88_RA
  · exact card_order88_RB
  · exact card_order88_RC
  · exact card_order88_RD
  · exact card_order88_RE
  · exact card_order88_RF
  · exact card_order88_RG
  · exact card_order88_RH
  · exact card_order88_RI
  · exact card_order88_RJ
  · exact card_order88_RK
  · exact card_order88_RL

/-- The displayed representatives exhaust the groups of order `88`, in `IsClassif` form. -/
theorem order88_complete (G : Type) [Group G] (hG : Nat.card G = 88) :
    ∃ i, Nonempty (G ≃* order88_reps i) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  rcases order88_classification (G := G) hG with h | h | h | h | h | h | h | h | h | h | h | h
  exacts [⟨0, by simpa [order88_reps, rep12] using h⟩,
    ⟨1, by simpa [order88_reps, rep12] using h⟩,
    ⟨2, by simpa [order88_reps, rep12] using h⟩,
    ⟨3, by simpa [order88_reps, rep12] using h⟩,
    ⟨4, by simpa [order88_reps, rep12] using h⟩,
    ⟨5, by simpa [order88_reps, rep12] using h⟩,
    ⟨6, by simpa [order88_reps, rep12] using h⟩,
    ⟨7, by simpa [order88_reps, rep12] using h⟩,
    ⟨8, by simpa [order88_reps, rep12] using h⟩,
    ⟨9, by simpa [order88_reps, rep12] using h⟩,
    ⟨10, by simpa [order88_reps, rep12] using h⟩,
    ⟨11, by simpa [order88_reps, rep12] using h⟩]

/-- Once pairwise non-isomorphism of the displayed representatives is known, they form a complete
classification of groups of order `88`. -/
theorem order88_isClassif_of_pairwise (hdistinct : PairwiseNonMulEquiv order88_reps) :
    IsClassif 88 order88_reps where
  card := card_order88_reps
  complete := order88_complete
  distinct := hdistinct

theorem order88_isClassif : IsClassif 88 order88_reps :=
  order88_isClassif_of_pairwise order88_reps_pairwise

end Smallgroups.UsefulTheorems
