/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.PrimeOrderClassification
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi

/-!
# Classification of groups of order `p²`

For a prime `p`, every group of order `p²` is abelian, and there are exactly **two** of them up to
isomorphism: the cyclic group `ℤ/p²` and the elementary abelian group `ℤ/p × ℤ/p`.

## Main results

* `prime_sq_mul_comm` — **a group of order `p²` is abelian** (via Mathlib's
  `IsPGroup.isMulCommutative_of_card_eq_prime_sq`, which goes through the nontrivial centre of a
  `p`-group).
* `prime_sq_classification` — **every group of order `p²` is isomorphic to `CyclicRep (p²)` or to
  `ElemAbelianRep p = CyclicRep p × CyclicRep p`.**  The proof splits on whether `G` is cyclic; in
  the non-cyclic case every element has order dividing `p`, so `G` is a `2`-dimensional vector space
  over the field `ℤ/p` and therefore `≅ ℤ/p × ℤ/p`.
* `prime_sq_distinct` — **the two representatives are not isomorphic** (`ℤ/p × ℤ/p` is not cyclic).
-/

namespace Smallgroups.UsefulTheorems

open Module

variable {G : Type*} [Group G] {p : ℕ}

/-- **A group of order `p²` is abelian.** -/
theorem prime_sq_mul_comm [Fact p.Prime] (hG : Nat.card G = p ^ 2) (a b : G) : a * b = b * a :=
  haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq hG
  mul_comm' a b

/-- The elementary abelian representative `ℤ/p × ℤ/p` of order `p²`. -/
abbrev ElemAbelianRep (p : ℕ) : Type := CyclicRep p × CyclicRep p

/-- `ElemAbelianRep p` has order `p²` (for `p ≠ 0`). -/
theorem card_elemAbelianRep {p : ℕ} (hp : p ≠ 0) : Nat.card (ElemAbelianRep p) = p ^ 2 := by
  change Nat.card (CyclicRep p × CyclicRep p) = p ^ 2
  rw [Nat.card_prod, card_cyclicRep hp]
  exact (pow_two p).symm

/-- **Classification of groups of order `p²`.** Every group of order `p²` is isomorphic either to
the cyclic group `CyclicRep (p²) = ℤ/p²` or to the elementary abelian group
`ElemAbelianRep p = ℤ/p × ℤ/p`. -/
theorem prime_sq_classification [hp : Fact p.Prime] (hG : Nat.card G = p ^ 2) :
    Nonempty (G ≃* CyclicRep (p ^ 2)) ∨ Nonempty (G ≃* ElemAbelianRep p) := by
  haveI : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero 2 hp.out.ne_zero)
  by_cases hcyc : IsCyclic G
  · exact Or.inl (cyclicRep_classification (pow_ne_zero 2 hp.out.ne_zero) hG)
  · refine Or.inr ?_
    -- Every element has order dividing `p`: order divides `p²` and cannot equal `p²`
    -- (else `G` would be cyclic).
    have hexp : ∀ g : G, g ^ p = 1 := by
      intro g
      have hdvd : orderOf g ∣ p ^ 2 := hG ▸ orderOf_dvd_natCard g
      obtain ⟨k, hk2, hke⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
      have hdp : orderOf g ∣ p := by
        interval_cases k
        · rw [pow_zero] at hke; rw [hke]; exact one_dvd p
        · rw [pow_one] at hke; rw [hke]
        · exact absurd (isCyclic_of_orderOf_eq_card g (hke.trans hG.symm)) hcyc
      exact orderOf_dvd_iff_pow_eq_one.mp hdp
    -- `G` is abelian, so view it additively and as a `ℤ/p`-vector space.
    letI : CommGroup G := IsPGroup.commGroupOfCardEqPrimeSq hG
    letI : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule (n := p) fun x => by
      calc p • x = Additive.ofMul (Additive.toMul x ^ p) := (ofMul_pow p (Additive.toMul x)).symm
        _ = Additive.ofMul (1 : G) := by rw [hexp (Additive.toMul x)]
        _ = 0 := ofMul_one
    -- `Additive G` is a finite `ℤ/p`-vector space (build the instances explicitly to avoid a
    -- stuck instance search).
    haveI : Finite (Additive G) := inferInstanceAs (Finite G)
    haveI hfg : Module.Finite (ZMod p) (Additive G) := by
      cases nonempty_fintype (Additive G)
      exact ⟨⟨Finset.univ, by rw [Finset.coe_univ, Submodule.span_univ]⟩⟩
    haveI hfree : Module.Free (ZMod p) (Additive G) :=
      Module.Free.of_divisionRing (ZMod p) (Additive G)
    -- Its dimension is `2`, since `p ^ dim = card = p²`.
    have hfin : finrank (ZMod p) (Additive G) = 2 := by
      have hcard : Nat.card (Additive G) = p ^ 2 := hG
      have hpow := @Module.natCard_eq_pow_finrank (ZMod p) (Additive G) _ _ _ hfg
      rw [Nat.card_zmod, hcard] at hpow
      exact (Nat.pow_right_injective hp.out.two_le hpow).symm
    -- A `2`-dimensional `ℤ/p`-space is `ℤ/p × ℤ/p`; convert back to a multiplicative group.
    have b : Basis (Fin 2) (ZMod p) (Additive G) :=
      @Module.finBasisOfFinrankEq (ZMod p) (Additive G) _ _ _ hfree _ hfg 2 hfin
    let e : Additive G ≃+ ZMod p × ZMod p :=
      (b.equivFun.trans (LinearEquiv.finTwoArrow (ZMod p) (ZMod p))).toAddEquiv
    exact ⟨(AddEquiv.toMultiplicativeRight e).trans (MulEquiv.prodMultiplicative (ZMod p) (ZMod p))⟩

/-- **The two order-`p²` representatives are not isomorphic:** `ℤ/p × ℤ/p` is not cyclic, while
`ℤ/p²` is. -/
theorem prime_sq_distinct [hp : Fact p.Prime] :
    ¬ Nonempty (CyclicRep (p ^ 2) ≃* ElemAbelianRep p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rintro ⟨e⟩
  haveI : IsCyclic (ElemAbelianRep p) := e.isCyclic.mp inferInstance
  have hcop : (Nat.card (CyclicRep p)).Coprime (Nat.card (CyclicRep p)) :=
    coprime_card_of_isCyclic_prod (CyclicRep p) (CyclicRep p)
  rw [card_cyclicRep hp.out.ne_zero] at hcop
  -- `Nat.Coprime p p` means `gcd p p = p = 1`, contradicting primality.
  have hp1 : p = 1 := by
    have h : Nat.gcd p p = 1 := hcop
    rwa [Nat.gcd_self] at h
  exact hp.out.ne_one hp1

end Smallgroups.UsefulTheorems
