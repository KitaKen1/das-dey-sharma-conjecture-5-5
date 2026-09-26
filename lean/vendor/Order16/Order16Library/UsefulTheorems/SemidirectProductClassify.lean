/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.End

/-!
# Classifying semidirect products by their action

After `SchurZassenhaus.lean` writes a group as `N ⋊[φ] H`, classification reduces to understanding
which actions `φ : H →* MulAut N` give isomorphic groups. This file develops the tools.

The action `φ` is recovered from the group together with its canonical inclusions by
`φ h n = (inr h * inl n * (inr h)⁻¹).left` (`SemidirectProduct.conjAction_eq`), so the
parametrisation is **faithful**: an isomorphism fixing `inl` and `inr` forces `φ = ψ`
(`semidirectProduct_action_inj`).

Two actions give *isomorphic* groups when they lie in the same orbit of `Aut N × Aut H` acting on
`Hom(H, Aut N)` by `(θ, σ) • φ = θ ∘ φ ∘ σ⁻¹` (up to conjugation). The constructive direction is:

* `semidirectProductCongr` — the master constructor: from `θ : N ≃* N'`, `σ : H ≃* H'` and a
  compatibility condition, build `N ⋊[φ] H ≃* N' ⋊[φ'] H'`;
* `semidirectProductCongrAut` — precomposing `φ` with an automorphism of `H` gives an isomorphic
  group;
* `semidirectProductCongrConj` — conjugating the action `φ` by an automorphism `θ` of `N` gives an
  isomorphic group;
* `semidirectProductCongr_eq` — equal actions give (canonically) isomorphic groups.

Together with the faithfulness statement, these reduce the isomorphism problem for `N ⋊ H` to the
orbit problem for `φ`.
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct

variable {N N' H H' : Type*} [Group N] [Group N'] [Group H] [Group H']
  {φ ψ : H →* MulAut N} {φ' : H' →* MulAut N'}

/-! ### The master isomorphism constructor -/

/-- **Comparing two semidirect products.** Given isomorphisms `θ : N ≃* N'` and `σ : H ≃* H'`
intertwining the actions (`θ ∘ φ h = φ' (σ h) ∘ θ` for all `h`), the map `(n, h) ↦ (θ n, σ h)` is an
isomorphism `N ⋊[φ] H ≃* N' ⋊[φ'] H'`. -/
noncomputable def semidirectProductCongr (θ : N ≃* N') (σ : H ≃* H')
    (compat : ∀ h, θ.toMonoidHom.comp (φ h).toMonoidHom
      = (φ' (σ h)).toMonoidHom.comp θ.toMonoidHom) :
    SemidirectProduct N H φ ≃* SemidirectProduct N' H' φ' :=
  MulEquiv.ofBijective (SemidirectProduct.map θ.toMonoidHom σ.toMonoidHom compat) <| by
    constructor
    · intro x y hxy
      have hl := congrArg SemidirectProduct.left hxy
      have hr := congrArg SemidirectProduct.right hxy
      exact SemidirectProduct.ext (θ.injective hl) (σ.injective hr)
    · intro z
      refine ⟨⟨θ.symm z.left, σ.symm z.right⟩, SemidirectProduct.ext ?_ ?_⟩
      · simp
      · simp

/-! ### Corollaries: the orbit moves -/

/-- Equal actions give (canonically) isomorphic semidirect products. -/
noncomputable def semidirectProductCongr_eq (h : φ = ψ) :
    SemidirectProduct N H φ ≃* SemidirectProduct N H ψ :=
  semidirectProductCongr (MulEquiv.refl N) (MulEquiv.refl H) (by subst h; intro g; ext n; rfl)

/-- **Precomposing the action with an automorphism of `H`.** For `σ : H ≃* H`,
`N ⋊[φ ∘ σ] H ≃* N ⋊[φ] H`. -/
noncomputable def semidirectProductCongrAut (σ : H ≃* H) :
    SemidirectProduct N H (φ.comp σ.toMonoidHom) ≃* SemidirectProduct N H φ :=
  semidirectProductCongr (MulEquiv.refl N) σ (by intro h; ext n; rfl)

/-- **Conjugating the action by an automorphism of `N`.** For `θ : N ≃* N`, conjugating `φ` by `θ`
gives an isomorphic group: `N ⋊[φ] H ≃* N ⋊[θ φ θ⁻¹] H`. -/
noncomputable def semidirectProductCongrConj (θ : N ≃* N) :
    SemidirectProduct N H φ ≃* SemidirectProduct N H ((MulAut.conj θ).toMonoidHom.comp φ) :=
  semidirectProductCongr θ (MulEquiv.refl H) (by
    intro h; ext n
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply]
    simp [MulAut.conj_apply])

/-! ### Faithfulness: the action is recovered from the group -/

/-- The action is recovered from the group structure: `φ h n` is the `N`-part of the conjugate
`inr h * inl n * (inr h)⁻¹`. -/
theorem conjAction_eq (h : H) (n : N) :
    φ h n = (inr h * inl n * inr h⁻¹ : SemidirectProduct N H φ).left := by
  rw [← SemidirectProduct.inl_aut]
  rfl

/-- **Faithfulness / the parametrisation is one-to-one.** An isomorphism `N ⋊[φ] H ≃* N ⋊[ψ] H`
fixing the canonical inclusions `inl` and `inr` forces the actions to agree. -/
theorem semidirectProduct_action_inj (e : SemidirectProduct N H φ ≃* SemidirectProduct N H ψ)
    (hl : ∀ n, e (inl n) = inl n) (hr : ∀ h, e (inr h) = inr h) : φ = ψ := by
  ext h n
  have key : (inl (φ h n) : SemidirectProduct N H ψ) = inl (ψ h n) := by
    have hcalc : e (inl (φ h n)) = (inl (ψ h n) : SemidirectProduct N H ψ) := by
      rw [SemidirectProduct.inl_aut, map_mul, map_mul, hr, hl, hr, ← SemidirectProduct.inl_aut]
    rwa [hl] at hcalc
  exact SemidirectProduct.inl_inj.mp key

/-! ### A characteristic normal subgroup has a well-defined complement

If `G = N ⋊ H₁ = N ⋊ H₂` (i.e. `H₁` and `H₂` are both complements of the *same* subgroup `N` in
the *same* ambient group `G`) and `N` is characteristic, then `H₁ ≅ H₂`: both realise the quotient
`G ⧸ N`. This does not even need `N` characteristic, just normal — `N.Characteristic` is a
convenient sufficient hypothesis since it gives `N.Normal` for free
(`Subgroup.normal_of_characteristic`), and it is what is available in practice (e.g. `N` is the
unique subgroup of its order, see `characteristic_of_coprime_index` below). -/

/-- **A characteristic subgroup has an isomorphism-unique complement.** If `H₁` and `H₂` are both
complements of the same characteristic subgroup `N` in `G`, then `H₁ ≅ H₂`. -/
theorem IsComplement'.mulEquiv_of_characteristic {G : Type*} [Group G] {N H1 H2 : Subgroup G}
    [N.Characteristic] (h1 : H1.IsComplement' N) (h2 : H2.IsComplement' N) :
    Nonempty (H1 ≃* H2) :=
  ⟨h1.QuotientMulEquiv.symm.trans h2.QuotientMulEquiv⟩

/-! ### Coprime order forces uniqueness, hence characteristic-ness

The hypothesis `N.Characteristic` in the theorem above is easiest to establish, in the
Schur–Zassenhaus setting used throughout this project, via **coprime order**: a normal subgroup
whose order is coprime to its index is the *unique* subgroup of that order, and is therefore fixed
by every automorphism. -/

/-- **A general helper.** A subgroup contained in another of the same (finite) cardinality equals
it. -/
private theorem eq_of_le_of_card_eq {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hle : H ≤ K) (hcard : Nat.card H = Nat.card K) : H = K := by
  apply SetLike.coe_injective
  have hH : Nat.card H = (↑H : Set G).ncard := Nat.card_coe_set_eq (↑H : Set G)
  have hK : Nat.card K = (↑K : Set G).ncard := Nat.card_coe_set_eq (↑K : Set G)
  exact Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hle) (by omega)

/-- **A normal subgroup with coprime index is the unique subgroup of its order.** If `N` is normal
in the finite group `G` with `Nat.card N` coprime to `N.index`, then any subgroup `K` with
`Nat.card K = Nat.card N` equals `N`. -/
theorem eq_of_normal_of_coprime_index_of_card_eq {G : Type*} [Group G] [Finite G]
    {N K : Subgroup G} [N.Normal] (hcop : Nat.Coprime (Nat.card N) N.index)
    (hK : Nat.card K = Nat.card N) : K = N := by
  have hle : K ≤ N := by
    intro x hx
    have hd1 : Nat.card (K.map (QuotientGroup.mk' N)) ∣ Nat.card K :=
      Subgroup.card_map_dvd K (QuotientGroup.mk' N)
    have hd2 : Nat.card (K.map (QuotientGroup.mk' N)) ∣ N.index := by
      rw [N.index_eq_card]
      exact (K.map (QuotientGroup.mk' N)).card_subgroup_dvd_card
    rw [hK] at hd1
    have h1 : Nat.card (K.map (QuotientGroup.mk' N)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    have hbot : K.map (QuotientGroup.mk' N) = ⊥ := Subgroup.card_eq_one.mp h1
    have hmem : QuotientGroup.mk' N x ∈ K.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  exact eq_of_le_of_card_eq hle (by rw [hK])

/-- **Coprime index implies characteristic.** A normal subgroup whose order is coprime to its
index is characteristic: any automorphism sends it to a normal subgroup of the same order, which
must be itself by uniqueness. -/
theorem characteristic_of_coprime_index {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (hcop : Nat.Coprime (Nat.card N) N.index) : N.Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ => ?_
  haveI : (N.map ϕ.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹N.Normal› ϕ.toMonoidHom ϕ.surjective
  have hcard : Nat.card (N.map ϕ.toMonoidHom) = Nat.card N :=
    Nat.card_congr (Equiv.Set.image ϕ N.carrier ϕ.injective).symm
  have hidx : (N.map ϕ.toMonoidHom).index = N.index := by
    have h1 := (N.map ϕ.toMonoidHom).card_mul_index
    have h2 := N.card_mul_index
    rw [hcard] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  exact eq_of_normal_of_coprime_index_of_card_eq (hidx ▸ hcop) hcard

/-! ### Transporting `H₁ ≅ H₂` across an abstract isomorphism of semidirect products -/

/-- **The complement of a coprime-order semidirect factor is well-defined up to isomorphism.**
If `Nat.card N` is coprime to `Nat.card H₂`, any isomorphism between `N ⋊[φ₁] H₁` and
`N ⋊[φ₂] H₂` forces `H₁ ≅ H₂`. (Only the target's coprimality is needed: the image of `N`'s copy
in the first group is forced, by uniqueness in the second group, to be `N`'s copy there.) -/
theorem semidirectProduct_congr_range {N H1 H2 : Type*} [Group N] [Group H1] [Group H2]
    [Finite N] [Finite H1] [Finite H2] {φ1 : H1 →* MulAut N} {φ2 : H2 →* MulAut N}
    (hcop2 : Nat.Coprime (Nat.card N) (Nat.card H2))
    (f : SemidirectProduct N H1 φ1 ≃* SemidirectProduct N H2 φ2) :
    Nonempty (H1 ≃* H2) := by
  haveI hfin1 : Finite (SemidirectProduct N H1 φ1) := by
    have : Nat.card (SemidirectProduct N H1 φ1) ≠ 0 := by
      rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
      exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
    exact Nat.finite_of_card_ne_zero this
  haveI hfin2 : Finite (SemidirectProduct N H2 φ2) :=
    Finite.of_equiv _ f.toEquiv
  set N1 : Subgroup (SemidirectProduct N H1 φ1) :=
    (SemidirectProduct.inl : N →* SemidirectProduct N H1 φ1).range with hN1def
  set N2 : Subgroup (SemidirectProduct N H2 φ2) :=
    (SemidirectProduct.inl : N →* SemidirectProduct N H2 φ2).range with hN2def
  haveI hN1normal : N1.Normal := by
    rw [hN1def, SemidirectProduct.range_inl_eq_ker_rightHom]; infer_instance
  haveI hN2normal : N2.Normal := by
    rw [hN2def, SemidirectProduct.range_inl_eq_ker_rightHom]; infer_instance
  have hcardN1 : Nat.card N1 = Nat.card N :=
    Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inl_injective).symm
  have hcardN2 : Nat.card N2 = Nat.card N :=
    Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inl_injective).symm
  have hidx2 : N2.index = Nat.card H2 := by
    have h1 := N2.card_mul_index
    have h2 : Nat.card (SemidirectProduct N H2 φ2) = Nat.card N * Nat.card H2 := by
      rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hcardN2, h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hcop2' : Nat.Coprime (Nat.card N2) N2.index := by rw [hcardN2, hidx2]; exact hcop2
  have hK : Nat.card (N1.map f.toMonoidHom) = Nat.card N2 := by
    rw [hcardN2, ← hcardN1]
    exact Nat.card_congr (Equiv.Set.image f.toMonoidHom N1.carrier f.injective).symm
  haveI hmapNormal : (N1.map f.toMonoidHom).Normal :=
    Subgroup.Normal.map hN1normal f.toMonoidHom f.surjective
  have heq : N1.map f.toMonoidHom = N2 :=
    eq_of_normal_of_coprime_index_of_card_eq hcop2' hK
  have hquot0 : (SemidirectProduct N H1 φ1) ⧸ N1 ≃*
      (SemidirectProduct N H2 φ2) ⧸ (N1.map f.toMonoidHom) :=
    QuotientGroup.congr N1 (N1.map f.toMonoidHom) f rfl
  have hquot : (SemidirectProduct N H1 φ1) ⧸ N1 ≃* (SemidirectProduct N H2 φ2) ⧸ N2 :=
    hquot0.trans (QuotientGroup.quotientMulEquivOfEq heq)
  have hker1 : (SemidirectProduct.rightHom : SemidirectProduct N H1 φ1 →* H1).ker = N1 :=
    (hN1def.trans SemidirectProduct.range_inl_eq_ker_rightHom).symm
  have hker2 : (SemidirectProduct.rightHom : SemidirectProduct N H2 φ2 →* H2).ker = N2 :=
    (hN2def.trans SemidirectProduct.range_inl_eq_ker_rightHom).symm
  have hquotH1 : H1 ≃* (SemidirectProduct N H1 φ1) ⧸ N1 :=
    (QuotientGroup.quotientKerEquivOfSurjective SemidirectProduct.rightHom
      SemidirectProduct.rightHom_surjective).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker1)
  have hquotH2 : (SemidirectProduct N H2 φ2) ⧸ N2 ≃* H2 :=
    (QuotientGroup.quotientMulEquivOfEq hker2).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective SemidirectProduct.rightHom
        SemidirectProduct.rightHom_surjective)
  exact ⟨hquotH1.trans (hquot.trans hquotH2)⟩

/-- **The normal semidirect factor is well-defined up to isomorphism.** If the normal factors
have the same cardinality and the target normal factor has coprime index, any isomorphism between
the semidirect products forces the normal factors to be isomorphic. -/
theorem semidirectProduct_congr_domain {N1 N2 H1 H2 : Type*}
    [Group N1] [Group N2] [Group H1] [Group H2]
    [Finite N1] [Finite N2] [Finite H1] [Finite H2]
    {φ1 : H1 →* MulAut N1} {φ2 : H2 →* MulAut N2}
    (hcard : Nat.card N1 = Nat.card N2)
    (hcop2 : Nat.Coprime (Nat.card N2) (Nat.card H2))
    (f : SemidirectProduct N1 H1 φ1 ≃* SemidirectProduct N2 H2 φ2) :
    Nonempty (N1 ≃* N2) := by
  haveI hfin1 : Finite (SemidirectProduct N1 H1 φ1) := by
    have : Nat.card (SemidirectProduct N1 H1 φ1) ≠ 0 := by
      rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
      exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
    exact Nat.finite_of_card_ne_zero this
  haveI hfin2 : Finite (SemidirectProduct N2 H2 φ2) :=
    Finite.of_equiv _ f.toEquiv
  set K1 : Subgroup (SemidirectProduct N1 H1 φ1) :=
    (SemidirectProduct.inl : N1 →* SemidirectProduct N1 H1 φ1).range with hK1def
  set K2 : Subgroup (SemidirectProduct N2 H2 φ2) :=
    (SemidirectProduct.inl : N2 →* SemidirectProduct N2 H2 φ2).range with hK2def
  haveI hK1normal : K1.Normal := by
    rw [hK1def, SemidirectProduct.range_inl_eq_ker_rightHom]; infer_instance
  haveI hK2normal : K2.Normal := by
    rw [hK2def, SemidirectProduct.range_inl_eq_ker_rightHom]; infer_instance
  have hcardK1 : Nat.card K1 = Nat.card N1 :=
    Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inl_injective).symm
  have hcardK2 : Nat.card K2 = Nat.card N2 :=
    Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inl_injective).symm
  have hidx2 : K2.index = Nat.card H2 := by
    have h1 := K2.card_mul_index
    have h2 : Nat.card (SemidirectProduct N2 H2 φ2) = Nat.card N2 * Nat.card H2 := by
      rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hcardK2, h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hcop2' : Nat.Coprime (Nat.card K2) K2.index := by
    rw [hcardK2, hidx2]
    exact hcop2
  have hK : Nat.card (K1.map f.toMonoidHom) = Nat.card K2 := by
    rw [hcardK2, ← hcard, ← hcardK1]
    exact Nat.card_congr (Equiv.Set.image f.toMonoidHom K1.carrier f.injective).symm
  haveI hmapNormal : (K1.map f.toMonoidHom).Normal :=
    Subgroup.Normal.map hK1normal f.toMonoidHom f.surjective
  have heq : K1.map f.toMonoidHom = K2 :=
    eq_of_normal_of_coprime_index_of_card_eq hcop2' hK
  let eK1 : N1 ≃* K1 :=
    MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ1))
  let eK2 : N2 ≃* K2 :=
    MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ2))
  exact ⟨eK1.trans ((f.subgroupMap K1).trans ((MulEquiv.subgroupCongr heq).trans eK2.symm))⟩

end Smallgroups.UsefulTheorems
