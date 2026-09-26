import CyclicIndexTwoRecognition

namespace Conjecture55OrderThirtyTwo
open Multiplicative Conjecture55CyclicIndexTwo
abbrev C16 := Multiplicative (ZMod 16)
abbrev C2 := Multiplicative (ZMod 2)
def x16 : C16 := ofAdd 1

/-- The four involutory power actions on C16. -/
def powerAut (k : ℕ) (hk : ∀ x : C16, x ^ (k * k) = x) : MulAut C16 where
  toFun x := x ^ k
  invFun x := x ^ k
  left_inv x := by change (x ^ k) ^ k = x; rw [← pow_mul]; exact hk x
  right_inv x := by change (x ^ k) ^ k = x; rw [← pow_mul]; exact hk x
  map_mul' x y := mul_pow x y k

lemma powerAut_sq (k : ℕ) (hk : ∀ x : C16, x ^ (k * k) = x) :
    powerAut k hk * powerAut k hk = 1 := by
  ext x
  change (x ^ k) ^ k = x
  rw [← pow_mul]
  exact hk x

noncomputable def c2Action (k : ℕ) (hk : ∀ x : C16, x ^ (k * k) = x) :
    C2 →* MulAut C16 where
  toFun g := if g = 1 then 1 else powerAut k hk
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with rfl | rfl <;>
      rcases c2_two_cases b with rfl | rfl <;>
      simp [show (ofAdd (1 : ZMod 2) : C2) ≠ 1 by decide,
        show (ofAdd (1 : ZMod 2) : C2) * ofAdd 1 = 1 by decide, powerAut_sq]

noncomputable abbrev action1 := c2Action 1 (by decide +kernel)
noncomputable abbrev action7 := c2Action 7 (by decide +kernel)
noncomputable abbrev action9 := c2Action 9 (by decide +kernel)
noncomputable abbrev action15 := c2Action 15 (by decide +kernel)
noncomputable abbrev Abelian32 := SemidirectProduct C16 C2 action1
noncomputable abbrev Semidihedral32 := SemidirectProduct C16 C2 action7
noncomputable abbrev Modular32 := SemidirectProduct C16 C2 action9
noncomputable abbrev Dihedral32 := SemidirectProduct C16 C2 action15

instance (φ : C2 →* MulAut C16) : Fintype (SemidirectProduct C16 C2 φ) :=
  Fintype.ofEquiv (C16 × C2) SemidirectProduct.equivProd.symm

lemma orderOf_x16 : orderOf x16 = 16 := by
  exact (orderOf_ofAdd_eq_addOrderOf _).trans (ZMod.addOrderOf_one 16)
lemma c16_decomp (p : C16) : p = x16 ^ p.toAdd.val := by
  have h : ∀ p : C16, p = x16 ^ p.toAdd.val := by decide +kernel
  exact h p

lemma c16_hom_ext {M : Type*} [Monoid M] {f g : C16 →* M}
    (h : f x16 = g x16) : f = g := by
  apply MonoidHom.ext
  intro p
  rw [c16_decomp p, map_pow, map_pow, h]

/-- Recognize a split extension with a cyclic subgroup of order sixteen. -/
lemma recog_c16_split {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (φ : C2 →* MulAut C16) {k : ℕ}
    (hφ : φ (ofAdd 1) x16 = x16 ^ k)
    (x t : G) (hx : orderOf x = 16) (ht2 : t ^ 2 = 1)
    (htx : t ∉ Subgroup.zpowers x) (hconj : t * x * t⁻¹ = x ^ k) :
    Nonempty (G ≃* SemidirectProduct C16 C2 φ) := by
  have hx' : x ^ 16 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hf : Function.Injective (zmodPowHom 16 x hx') :=
    zmodPowHom_injective (by norm_num) x hx' hx
  have hfx : zmodPowHom 16 x hx' x16 = x := zmodPowHom_gen (by norm_num) x hx'
  have hfr : t ∉ (zmodPowHom 16 x hx').range := by
    rintro ⟨a, ha⟩
    apply htx
    rw [← ha, zmodPowHom_eval]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  have hhom : (MulAut.conj t).toMonoidHom.comp (zmodPowHom 16 x hx') =
      (zmodPowHom 16 x hx').comp (φ (ofAdd 1)).toMonoidHom := by
    apply c16_hom_ext
    change MulAut.conj t (zmodPowHom 16 x hx' x16) = zmodPowHom 16 x hx' (φ (ofAdd 1) x16)
    rw [hfx, hφ, MulAut.conj_apply, hconj, map_pow, hfx]
  exact recog_split_c2 φ (zmodPowHom 16 x hx') hf t ht2 hfr (fun n => by
    simpa [MulAut.conj_apply] using DFunLike.congr_fun hhom n)
    (by rw [hcard, Nat.card_eq_fintype_card]; decide)

/-- Identification with the conventional abelian and dihedral models. -/
noncomputable def abelian32Equiv : Abelian32 ≃* Multiplicative (ZMod 16 × ZMod 2) where
  toFun g := ofAdd (g.left.toAdd, g.right.toAdd)
  invFun a := ⟨ofAdd a.toAdd.1, ofAdd a.toAdd.2⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

noncomputable def dihedral32Equiv : Dihedral32 ≃* DihedralGroup 16 where
  toFun g := if g.right.toAdd = 0 then DihedralGroup.r g.left.toAdd
    else DihedralGroup.sr (-g.left.toAdd)
  invFun
    | DihedralGroup.r i => ⟨ofAdd i, ofAdd 0⟩
    | DihedralGroup.sr i => ⟨ofAdd (-i), ofAdd 1⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

#print axioms powerAut_sq
#print axioms orderOf_x16
#print axioms recog_c16_split
#print axioms abelian32Equiv
#print axioms dihedral32Equiv
end Conjecture55OrderThirtyTwo
