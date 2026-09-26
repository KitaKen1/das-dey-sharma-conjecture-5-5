/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.PrimeSqPrime
import Order16Library.UsefulTheorems.PrimePairNonabelian
import Order16Library.UsefulTheorems.Counting
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.ZMod.Basic

/-!
# Groups of order `2 p²` (`p` an odd prime): the five representatives

For an odd prime `p`, there are exactly **five** groups of order `2 p²` up to isomorphism. This file
sets up the five representatives and proves each has order `2 p²`.

* `R1 = ℤ/2p²` (cyclic),
* `R2 = ℤ/p × ℤ/2p` (abelian, non-cyclic),
* `R3 = D_{p²}` (dihedral of order `2p²`; Sylow-`p` cyclic),
* `R4 = D_p × ℤ/p` (Sylow-`p` elementary abelian, center `ℤ/p`),
* `R5 = (ℤ/p)² ⋊₋₁ ℤ/2` (generalized dihedral; center trivial).

By `psq_semidirectProduct` (with `q = 2`, where `p ∤ q − 1` is automatic) every group of order
`2 p²` is `P ⋊[φ] ℤ/2` with `P` the abelian Sylow-`p` subgroup, so the classification reduces to
the involution `φ(1) ∈ Aut P`.
-/

namespace Smallgroups.UsefulTheorems

open scoped BigOperators

/-! ### The inversion action (for the generalized dihedral representative) -/

/-- Inversion `x ↦ x⁻¹` as an automorphism of a commutative group. -/
def invAut (G : Type*) [CommGroup G] : MulAut G where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' := mul_inv

@[simp] theorem invAut_apply {G : Type*} [CommGroup G] (x : G) : invAut G x = x⁻¹ := rfl

theorem invAut_sq (G : Type*) [CommGroup G] : invAut G ^ 2 = 1 := by
  ext x; simp [sq]

/-- The action of `ℤ/2` on a commutative group by inversion. -/
noncomputable def invActionHom (G : Type*) [CommGroup G] :
    Multiplicative (ZMod 2) →* MulAut G :=
  MonoidHom.mk' (fun x => invAut G ^ (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add (invAut_sq G) (Multiplicative.toAdd a) (Multiplicative.toAdd b))

/-! ### The five representatives -/

variable (p : ℕ)

/-- `ℤ/2p²` (cyclic). -/
abbrev R1 : Type := Multiplicative (ZMod (2 * p ^ 2))
/-- `ℤ/p × ℤ/2p` (abelian, non-cyclic). -/
abbrev R2 : Type := Multiplicative (ZMod p) × Multiplicative (ZMod (2 * p))
/-- `D_{p²}` (dihedral of order `2p²`). -/
abbrev R3 : Type := DihedralGroup (p ^ 2)
/-- `D_p × ℤ/p`. -/
abbrev R4 : Type := DihedralGroup p × Multiplicative (ZMod p)
/-- `(ℤ/p)² ⋊₋₁ ℤ/2` (generalized dihedral). -/
noncomputable abbrev R5 : Type :=
  Multiplicative (ZMod p × ZMod p) ⋊[invActionHom (Multiplicative (ZMod p × ZMod p))]
    Multiplicative (ZMod 2)

/-! ### Cardinalities -/

variable [Fact p.Prime]

private theorem card_mult_zmod (n : ℕ) [NeZero n] : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem two_psq_ne : 2 * p ^ 2 ≠ 0 := by
  have := (Fact.out (p := p.Prime)).pos; positivity

theorem card_R1 : Nat.card (R1 p) = 2 * p ^ 2 := by
  haveI : NeZero (2 * p ^ 2) := ⟨two_psq_ne p⟩
  exact card_mult_zmod _

theorem card_R2 : Nat.card (R2 p) = 2 * p ^ 2 := by
  have hp := (Fact.out (p := p.Prime)).pos
  haveI : NeZero p := ⟨hp.ne'⟩
  haveI : NeZero (2 * p) := ⟨by positivity⟩
  rw [Nat.card_prod, card_mult_zmod, card_mult_zmod]; ring

omit [Fact p.Prime] in
theorem card_R3 : Nat.card (R3 p) = 2 * p ^ 2 := DihedralGroup.nat_card

theorem card_R4 : Nat.card (R4 p) = 2 * p ^ 2 := by
  have hp := (Fact.out (p := p.Prime)).pos
  haveI : NeZero p := ⟨hp.ne'⟩
  rw [Nat.card_prod, DihedralGroup.nat_card, card_mult_zmod]; ring

theorem card_R5 : Nat.card (R5 p) = 2 * p ^ 2 := by
  have hp := (Fact.out (p := p.Prime)).pos
  haveI : NeZero p := ⟨hp.ne'⟩
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, card_mult_zmod 2,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
  ring

/-! ### Commutativity / non-commutativity -/

omit [Fact p.Prime] in
theorem R1_comm : ∀ a b : R1 p, a * b = b * a := fun a b => mul_comm a b

theorem R2_comm : ∀ a b : R2 p, a * b = b * a := fun a b => mul_comm a b

variable {p}

private theorem two_ne_zero_p (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring, Ne,
    CharP.cast_eq_zero_iff (ZMod p) p]
  exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

private theorem two_ne_zero_psq (hp2 : p ≠ 2) : (2 : ZMod (p ^ 2)) ≠ 0 := by
  have hp : p.Prime := Fact.out
  rw [show (2 : ZMod (p ^ 2)) = ((2 : ℕ) : ZMod (p ^ 2)) by push_cast; ring, Ne,
    CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
  intro hd
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have : p ^ 2 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  nlinarith [h3]

/-- `D_{p²}` is non-abelian. -/
theorem R3_not_comm (hp2 : p ≠ 2) : ¬ ∀ a b : R3 p, a * b = b * a := by
  intro h
  have key := h (DihedralGroup.r 1) (DihedralGroup.sr 0)
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq] at key
  apply two_ne_zero_psq hp2
  linear_combination -key

/-- `D_p × ℤ/p` is non-abelian. -/
theorem R4_not_comm (hp2 : p ≠ 2) : ¬ ∀ a b : R4 p, a * b = b * a := by
  intro h
  have key := h (DihedralGroup.r 1, 1) (DihedralGroup.sr 0, 1)
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk.injEq] at key
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq] at key
  apply two_ne_zero_p hp2
  linear_combination -key.1

@[simp] theorem invActionHom_gen {G : Type*} [CommGroup G] :
    invActionHom G (Multiplicative.ofAdd 1) = invAut G := by
  change invAut G ^ ((1 : ZMod 2).val) = invAut G
  rw [show (1 : ZMod 2).val = 1 from by decide, pow_one]

/-- The generalized dihedral group `(ℤ/p)² ⋊₋₁ ℤ/2` is non-abelian. -/
theorem R5_not_comm (hp2 : p ≠ 2) : ¬ ∀ a b : R5 p, a * b = b * a := by
  intro h
  set N := Multiplicative (ZMod p × ZMod p)
  set n : N := Multiplicative.ofAdd ((1, 0) : ZMod p × ZMod p) with hn
  have key := h (SemidirectProduct.inr (Multiplicative.ofAdd 1)) (SemidirectProduct.inl n)
  have hleft := congrArg SemidirectProduct.left key
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, invActionHom_gen, invAut_apply,
    map_one, one_mul, mul_one] at hleft
  -- `hleft : n⁻¹ = n`, i.e. `n * n = 1`, contradicting `(2,0) ≠ 0`
  apply two_ne_zero_p hp2
  have hn2 : n * n = 1 := by nth_rewrite 1 [← hleft]; exact inv_mul_cancel n
  have h0 : Multiplicative.toAdd (n * n) = 0 := by rw [hn2]; rfl
  rw [toAdd_mul, hn] at h0
  simp only [toAdd_ofAdd, Prod.mk_add_mk] at h0
  have hfst := congrArg Prod.fst h0
  simp only [Prod.fst_zero] at hfst
  linear_combination hfst

/-! ### Distinguishing the two abelian representatives -/

instance R1_isCyclic : IsCyclic (R1 p) := inferInstance

theorem R2_not_isCyclic : ¬ IsCyclic (R2 p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (2 * p) := ⟨Nat.mul_ne_zero (by norm_num) hp.pos.ne'⟩
  intro h
  have hcop := coprime_card_of_isCyclic_prod
    (Multiplicative (ZMod p)) (Multiplicative (ZMod (2 * p)))
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at hcop
  rw [Nat.coprime_mul_iff_right] at hcop
  exact absurd ((Nat.gcd_self p).symm.trans hcop.2) hp.one_lt.ne'

/-- `ℤ/2p²` (cyclic) is not isomorphic to `ℤ/p × ℤ/2p` (non-cyclic). -/
theorem R1_not_mulEquiv_R2 : ¬ Nonempty (R1 p ≃* R2 p) := by
  rintro ⟨e⟩
  exact R2_not_isCyclic (isCyclic_of_surjective e e.surjective)

/-! ### Distinguishing the three non-abelian representatives by element orders

`D_{p²}` has an element of order `p²` (the others do not); `D_p × ℤ/p` has an element of order `2p`
(the others do not). Both invariants are preserved by isomorphism (`orderOf_injective`). -/

/-- Two groups with a separating "order-`m` element exists" status are non-isomorphic. -/
theorem not_mulEquiv_of_orderOf {A B : Type*} [Group A] [Group B] {m : ℕ}
    (hA : ∃ g : A, orderOf g = m) (hB : ∀ g : B, orderOf g ≠ m) : ¬ Nonempty (A ≃* B) := by
  rintro ⟨e⟩
  obtain ⟨g, hg⟩ := hA
  refine hB (e g) ?_
  rw [← hg]
  exact orderOf_injective e.toMonoidHom e.injective g

/-- From `∀ g, g^a = 1`, no element has an order `m` not dividing `a`. -/
theorem orderOf_ne_of_pow {G : Type*} [Group G] {a m : ℕ} (h : ∀ g : G, g ^ a = 1)
    (hm : ¬ m ∣ a) (g : G) : orderOf g ≠ m :=
  fun hg => hm (hg ▸ orderOf_dvd_of_pow_eq_one (h g))

/-- From `∀ g, g^a = 1 ∨ g^b = 1`, no element has an order `m` dividing neither `a` nor `b`. -/
theorem orderOf_ne_of_pow_or {G : Type*} [Group G] {a b m : ℕ} (h : ∀ g : G, g ^ a = 1 ∨ g ^ b = 1)
    (ha : ¬ m ∣ a) (hb : ¬ m ∣ b) (g : G) : orderOf g ≠ m := by
  intro hg
  rcases h g with h1 | h1
  · exact ha (hg ▸ orderOf_dvd_of_pow_eq_one h1)
  · exact hb (hg ▸ orderOf_dvd_of_pow_eq_one h1)

private theorem hp3 (hp2 : p ≠ 2) : 3 ≤ p := by
  have := (Fact.out (p := p.Prime)).two_le; omega

/-- Every element of `(ℤ/p)²` (multiplicative) is `p`-torsion. -/
private theorem pow_p_eq_one_zmodsq (m : Multiplicative (ZMod p × ZMod p)) : m ^ p = 1 := by
  have h0 : p • m.toAdd = (0 : ZMod p × ZMod p) := Prod.ext (by simp) (by simp)
  rw [← ofAdd_toAdd m, ← ofAdd_nsmul, h0, ofAdd_zero]

omit [Fact p.Prime] in
/-- `D_{p²}` has an element of order `p²`. -/
theorem R3_hasOrderPSq : ∃ g : R3 p, orderOf g = p ^ 2 :=
  ⟨DihedralGroup.r 1, DihedralGroup.orderOf_r_one⟩

/-- Every element of `D_p × ℤ/p` is killed by `2p` (so none has order `p²`). -/
theorem R4_pow (g : R4 p) : g ^ (2 * p) = 1 := by
  obtain ⟨x, y⟩ := g
  have hx : x ^ (2 * p) = 1 := by
    rw [← DihedralGroup.card (n := p)]; exact pow_card_eq_one
  have hy : y ^ (2 * p) = 1 := by
    have hyp : y ^ p = 1 := by
      have h1 : y ^ Fintype.card (Multiplicative (ZMod p)) = 1 := pow_card_eq_one
      rwa [Fintype.card_multiplicative, ZMod.card] at h1
    rw [mul_comm, pow_mul, hyp, one_pow]
  rw [Prod.pow_mk, hx, hy]; rfl

/-- Every element of the generalized dihedral group satisfies `g^p = 1` or `g² = 1` (so none has
order `p²` or `2p`). -/
theorem R5_pow (g : R5 p) : g ^ p = 1 ∨ g ^ 2 = 1 := by
  have hcase : g.right = 1 ∨ g.right = Multiplicative.ofAdd 1 := by
    obtain ⟨x, hx⟩ : ∃ x : ZMod 2, Multiplicative.ofAdd x = g.right := ⟨g.right.toAdd, by simp⟩
    revert hx; fin_cases x <;> intro hx
    · exact Or.inl (by rw [← hx]; rfl)
    · exact Or.inr hx.symm
  rcases hcase with hr | hr
  · left
    have hg : g = SemidirectProduct.inl g.left :=
      SemidirectProduct.ext rfl (by rw [hr]; rfl)
    rw [hg, ← map_pow, pow_p_eq_one_zmodsq, map_one]
  · right
    rw [sq]
    refine SemidirectProduct.ext ?_ ?_
    · simp [SemidirectProduct.mul_left, hr, invActionHom_gen]
    · rw [SemidirectProduct.mul_right, hr, SemidirectProduct.one_right]; decide

/-- `D_p × ℤ/p` has an element of order `2p`. -/
theorem R4_hasOrder2p (hp2 : p ≠ 2) : ∃ g : R4 p, orderOf g = 2 * p := by
  have hp : p.Prime := Fact.out
  refine ⟨(DihedralGroup.sr 0, Multiplicative.ofAdd 1),
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (R4_pow _)) ?_⟩
  set o := orderOf ((DihedralGroup.sr (0 : ZMod p), Multiplicative.ofAdd (1 : ZMod p)) : R4 p)
  have hpow : ((DihedralGroup.sr (0 : ZMod p), Multiplicative.ofAdd (1 : ZMod p)) : R4 p) ^ o = 1 :=
    pow_orderOf_eq_one _
  rw [Prod.pow_mk, Prod.ext_iff] at hpow
  simp only [Prod.fst_one, Prod.snd_one] at hpow
  have h2 : 2 ∣ o := DihedralGroup.orderOf_sr (0 : ZMod p) ▸ orderOf_dvd_of_pow_eq_one hpow.1
  have hpd : p ∣ o := by
    have := orderOf_dvd_of_pow_eq_one hpow.2
    rwa [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one] at this
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)) h2 hpd

/-! ### Splitting the five representatives into abelian and non-abelian families

We feed `PairwiseNonMulEquiv.sum`: the abelian pair `[R1, R2]` and the non-abelian triple
`[R3, R4, R5]`, which are disjoint because the first are commutative and the second are not. This
replaces the six individual abelian-vs-non-abelian non-isomorphism checks with a single appeal to
`pairwise_disjoint_of_comm_noncomm`. -/

/-- The abelian representatives `[ℤ/2p², ℤ/p × ℤ/2p]`. -/
abbrev abelianFam (p : ℕ) : Fin 2 → Type := rep2 (R1 p) (R2 p)

/-- The non-abelian representatives `[D_{p²}, D_p × ℤ/p, gen. dihedral]`. -/
noncomputable abbrev nonabFam (p : ℕ) : Fin 3 → Type := rep3 (R3 p) (R4 p) (R5 p)

theorem abelianFam_comm : ∀ i, ∀ a b : abelianFam p i, a * b = b * a := by
  intro i; fin_cases i
  · exact R1_comm p
  · exact R2_comm p

theorem nonabFam_noncomm (hp2 : p ≠ 2) : ∀ j, ¬ ∀ a b : nonabFam p j, a * b = b * a := by
  intro j; fin_cases j
  · exact R3_not_comm hp2
  · exact R4_not_comm hp2
  · exact R5_not_comm hp2

/-- The abelian and non-abelian families are disjoint (no abelian rep is `≃*` a non-abelian one). -/
theorem abelian_nonab_disjoint (hp2 : p ≠ 2) :
    ∀ i j, ¬ Nonempty (abelianFam p i ≃* nonabFam p j) :=
  pairwise_disjoint_of_comm_noncomm (abelianFam_comm (p := p)) (nonabFam_noncomm hp2)

/-- The two abelian representatives are non-isomorphic (cyclic vs non-cyclic). -/
theorem abelianFam_pairwise : PairwiseNonMulEquiv (abelianFam p) := by
  intro i j hiso
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hiso R1_not_mulEquiv_R2
  · exact absurd ⟨hiso.some.symm⟩ R1_not_mulEquiv_R2
  · rfl

/-- The three non-abelian representatives are pairwise non-isomorphic (`D_{p²}` alone has an
order-`p²` element; `D_p × ℤ/p` alone has an order-`2p` element). -/
theorem nonabFam_pairwise (hp2 : p ≠ 2) : PairwiseNonMulEquiv (nonabFam p) := by
  have hp : p.Prime := Fact.out
  have h3 := hp3 hp2
  have h34 : ¬ Nonempty (R3 p ≃* R4 p) :=
    not_mulEquiv_of_orderOf R3_hasOrderPSq
      (orderOf_ne_of_pow R4_pow (fun h => by have := Nat.le_of_dvd (by positivity) h; nlinarith))
  have h35 : ¬ Nonempty (R3 p ≃* R5 p) :=
    not_mulEquiv_of_orderOf R3_hasOrderPSq
      (orderOf_ne_of_pow_or R5_pow
        (fun h => by have := Nat.le_of_dvd hp.pos h; nlinarith)
        (fun h => by have := Nat.le_of_dvd (by norm_num) h; nlinarith))
  have h45 : ¬ Nonempty (R4 p ≃* R5 p) :=
    not_mulEquiv_of_orderOf (R4_hasOrder2p hp2)
      (orderOf_ne_of_pow_or R5_pow
        (fun h => by have := Nat.le_of_dvd hp.pos h; omega)
        (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  intro i j hiso
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd hiso ‹_›
      | exact absurd (Nonempty.intro hiso.some.symm) ‹_›

/-- **The five representatives of order `2p²` are pairwise non-isomorphic**, assembled by
`PairwiseNonMulEquiv.sum` from the abelian pair, the non-abelian triple, and their disjointness. -/
theorem all_pairwise (hp2 : p ≠ 2) :
    PairwiseNonMulEquiv (Sum.elim (abelianFam p) (nonabFam p)) :=
  abelianFam_pairwise.sum (nonabFam_pairwise hp2) (abelian_nonab_disjoint hp2)

end Smallgroups.UsefulTheorems
