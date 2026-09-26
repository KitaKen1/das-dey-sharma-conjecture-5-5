import Mathlib

/-!
# Das–Dey–Sharma Conjecture 5.5 from the odd order theorem

For a finite group `G`, if the number of cyclic subgroups is less than
`2 ^ (ω(|G|) + 2)`, then `G` is solvable (Formal Conjectures,
`Arxiv.«2604.08040».solvable_of_cyc_lt`).

This file proves the statement assuming the Feit–Thompson odd order theorem as an
explicit hypothesis, stated exactly as the Lean Eval problem `feit_thompson`.
No other classification result is assumed, and the only import is Mathlib.
The final theorems and their axiom reports are at the end of the file.

The source consists of 50 modules, concatenated in dependency order.
Lean `v4.35.0-rc3`, Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.
-/

/-! ### Module `Conjecture55Foundation` -/
section
/-
Copyright 2026 The Formal Conjectures Authors and contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
The target and, in the standalone version, the two definitions are adapted from
FormalConjectures/Arxiv/2604.08040/Conjecture5_5.lean at
8323e878b83fcd7f4a448256069352a265460d75.
-/

/-!
Foundational reductions and counts for the complete Conjecture 5.5 proof.
The final theorem is in Conjecture55Lean4Web.lean.
-/

#eval Lean.versionString

namespace Conjecture55Lean4Web

/-- Exact copy of the FC definition of the number of cyclic subgroups. -/
noncomputable def cyc (G : Type*) [Group G] : ℕ :=
  Nat.card {H : Subgroup G // IsCyclic H}

/-- Exact copy of the FC definition of the number of distinct prime factors. -/
noncomputable def numPrimeFactors (G : Type*) [Fintype G] : ℕ :=
  (Fintype.card G).primeFactors.card

noncomputable section

/-- The mathematical proposition on the right-hand side of the FC target. -/
def Conjecture55 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G],
    cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G

/-- The contrapositive formulation; this is equivalent to the whole conjecture. -/
def NonSolvableLowerBound : Prop :=
  ∀ (G : Type) [Group G] [Fintype G],
    ¬ Group.IsSolvable G → 2 ^ (numPrimeFactors G + 2) ≤ cyc G

/-- A logical reformulation, not a proof of either side. -/
theorem conjecture55_iff_lower_bound : Conjecture55 ↔ NonSolvableLowerBound := by
  constructor
  · intro h G _ _ hns
    by_contra hlt
    exact hns (h G (Nat.lt_of_not_ge hlt))
  · intro h G _ _ hlt
    by_contra hns
    exact (Nat.not_lt_of_ge (h G hns)) hlt

section CyclicSubgroups

variable {G H : Type*} [Group G] [Group H]

/-- The map induced by a homomorphism on the set of cyclic subgroups. -/
def cyclicSubgroupMap (f : G →* H) :
    {K : Subgroup G // IsCyclic K} → {K : Subgroup H // IsCyclic K} := fun K ↦
  ⟨K.1.map f, by
    obtain ⟨g, hg⟩ := K.1.isCyclic_iff_exists_zpowers_eq_top.mp K.2
    apply (K.1.map f).isCyclic_iff_exists_zpowers_eq_top.mpr
    exact ⟨f g, by rw [← MonoidHom.map_zpowers, hg]⟩⟩

/-- Injective homomorphisms induce injections on cyclic subgroups. -/
theorem cyclicSubgroupMap_injective (f : G →* H) (hf : Function.Injective f) :
    Function.Injective (cyclicSubgroupMap f) := by
  intro K L h
  apply Subtype.ext
  exact Subgroup.map_injective hf (congrArg Subtype.val h)

/-- Lift a generator of a cyclic subgroup along a surjective homomorphism. -/
theorem cyclicSubgroupMap_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (cyclicSubgroupMap f) := by
  intro K
  obtain ⟨h, hh⟩ := K.1.isCyclic_iff_exists_zpowers_eq_top.mp K.2
  obtain ⟨g, hg⟩ := hf h
  refine ⟨⟨Subgroup.zpowers g, inferInstance⟩, ?_⟩
  apply Subtype.ext
  change (Subgroup.zpowers g).map f = K.1
  rw [MonoidHom.map_zpowers, hg, hh]

variable [Finite G] [Finite H]

omit [Finite G] in
/-- A finite group embedding cannot decrease the number of cyclic subgroups. -/
theorem cyc_le_of_injective (f : G →* H) (hf : Function.Injective f) :
    cyc G ≤ cyc H := by
  exact Nat.card_le_card_of_injective (cyclicSubgroupMap f)
    (cyclicSubgroupMap_injective f hf)

omit [Finite H] in
/-- Passing to a homomorphic image cannot increase the cyclic subgroup count. -/
theorem cyc_le_of_surjective (f : G →* H) (hf : Function.Surjective f) :
    cyc H ≤ cyc G := by
  exact Nat.card_le_card_of_surjective (cyclicSubgroupMap f)
    (cyclicSubgroupMap_surjective f hf)

/-- Cyclic subgroup counts are invariant under group isomorphism. -/
theorem cyc_eq_of_mulEquiv (e : G ≃* H) : cyc G = cyc H := by
  exact Nat.le_antisymm (cyc_le_of_injective e.toMonoidHom e.injective)
    (cyc_le_of_injective e.symm.toMonoidHom e.symm.injective)

end CyclicSubgroups

section CoprimeDoubling

open SemidirectProduct

variable {N H : Type*} [Group N] [Group H] [Finite N] [Finite H]
variable (φ : H →* MulAut N)

local instance : Finite (N ⋊[φ] H) := Finite.of_equiv (N × H) equivProd.symm

lemma two_lifts [Nontrivial N] (hc : (Nat.card N).Coprime (Nat.card H)) (h : H) :
    ∃ y : N ⋊[φ] H,
      rightHom y = h ∧ Subgroup.zpowers y ≠ Subgroup.zpowers (inr h : N ⋊[φ] H) := by
  classical
  by_cases hcomm : ∀ n : N, Commute (inl n : N ⋊[φ] H) (inr h)
  · obtain ⟨n, hn⟩ := exists_ne (1 : N)
    refine ⟨inl n * inr h, by simp, ?_⟩
    intro heq
    have horder : orderOf (inl n * inr h : N ⋊[φ] H) =
        orderOf (inr h : N ⋊[φ] H) := by
      simpa only [Nat.card_zpowers] using congrArg (fun K : Subgroup (N ⋊[φ] H) ↦ Nat.card K) heq
    have hco : (orderOf (inl n : N ⋊[φ] H)).Coprime (orderOf (inr h : N ⋊[φ] H)) := by
      rw [orderOf_injective inl inl_injective, orderOf_injective inr inr_injective]
      exact hc.of_dvd (orderOf_dvd_natCard n) (orderOf_dvd_natCard h)
    rw [(hcomm n).orderOf_mul_eq_mul_orderOf_of_coprime hco,
      orderOf_injective inl inl_injective, orderOf_injective inr inr_injective] at horder
    have ho := orderOf_pos h
    have hnorder := orderOf_eq_one_iff.ne.mpr hn
    have : 1 < orderOf n := by have := orderOf_pos n; omega
    nlinarith
  · push Not at hcomm
    obtain ⟨n, hn⟩ := hcomm
    refine ⟨inl n * inr h * (inl n)⁻¹, by simp, ?_⟩
    intro heq
    have hm : inl n * inr h * (inl n)⁻¹ ∈ Subgroup.zpowers (inr h : N ⋊[φ] H) := by
      rw [← heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hzH : h ^ z = h := by
      simpa only [map_zpow, map_mul, map_inv, rightHom_inl, rightHom_inr,
        one_mul, inv_one, mul_one] using congrArg (rightHom : N ⋊[φ] H →* H) hz
    have hzG : (inr h : N ⋊[φ] H) ^ z = inr h := by
      simpa only [map_zpow] using congrArg (inr : H →* N ⋊[φ] H) hzH
    have he : inl n * inr h * (inl n)⁻¹ = (inr h : N ⋊[φ] H) := hz.symm.trans hzG
    apply hn
    change inl n * inr h = (inr h : N ⋊[φ] H) * inl n
    calc
      _ = (inl n * inr h * (inl n)⁻¹) * inl n := by simp [mul_assoc]
      _ = _ := by rw [he]

lemma two_mul_card_le_of_two_lifts {α β : Type*} [Finite α] (f : α → β)
    (hf : ∀ b, ∃ x y, x ≠ y ∧ f x = b ∧ f y = b) :
    2 * Nat.card β ≤ Nat.card α := by
  classical
  choose x y hne hx hy using hf
  let lift : Bool × β → α := fun b ↦ if b.1 then x b.2 else y b.2
  have hlift : ∀ b, f (lift b) = b.2 := by
    rintro ⟨b, k⟩
    cases b <;> simp [lift, hx, hy]
  have hi : Function.Injective lift := by
    rintro ⟨b, k⟩ ⟨c, l⟩ he
    have hk : k = l := by simpa only [hlift] using congrArg f he
    subst l
    have hbc : b = c := by
      cases b <;> cases c
      · rfl
      · exact False.elim (hne k (by simpa [lift] using he.symm))
      · exact False.elim (hne k (by simpa [lift] using he))
      · rfl
    subst c
    rfl
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_le_card_of_injective lift hi

lemma two_cyclic_lifts [Nontrivial N] (hc : (Nat.card N).Coprime (Nat.card H))
    (K : {K : Subgroup H // IsCyclic K}) :
    ∃ L M : {L : Subgroup (N ⋊[φ] H) // IsCyclic L},
      L ≠ M ∧ L.1.map rightHom = K.1 ∧ M.1.map rightHom = K.1 := by
  obtain ⟨h, hh⟩ := K.1.isCyclic_iff_exists_zpowers_eq_top.mp K.2
  obtain ⟨y, hy, hne⟩ := two_lifts φ hc h
  refine ⟨⟨Subgroup.zpowers y, inferInstance⟩,
    ⟨Subgroup.zpowers (inr h), inferInstance⟩, ?_, ?_, ?_⟩
  · exact fun he ↦ hne (congrArg Subtype.val he)
  · rw [MonoidHom.map_zpowers, hy, hh]
  · rw [MonoidHom.map_zpowers, rightHom_inr, hh]

lemma coprime_semidirect_doubling [Nontrivial N]
    (hc : (Nat.card N).Coprime (Nat.card H)) :
    2 * cyc H ≤ cyc (N ⋊[φ] H) := by
  classical
  let f : {L : Subgroup (N ⋊[φ] H) // IsCyclic L} →
      {K : Subgroup H // IsCyclic K} := fun L ↦ ⟨L.1.map rightHom, by
    obtain ⟨g, hg⟩ := L.1.isCyclic_iff_exists_zpowers_eq_top.mp L.2
    apply (L.1.map rightHom).isCyclic_iff_exists_zpowers_eq_top.mpr
    exact ⟨rightHom g, by rw [← MonoidHom.map_zpowers, hg]⟩⟩
  apply two_mul_card_le_of_two_lifts f
  intro K
  obtain ⟨L, M, hne, hL, hM⟩ := two_cyclic_lifts φ hc K
  exact ⟨L, M, hne, Subtype.ext hL, Subtype.ext hM⟩

lemma normal_hall_doubling {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [Nontrivial N]
    (hc : (Nat.card N).Coprime N.index) : 2 * cyc (G ⧸ N) ≤ cyc G := by
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hc
  let φ : H →* MulAut N := N.normalizerMonoidHom.comp
    (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))
  have hcop : (Nat.card N).Coprime (Nat.card H) := by
    rwa [hH.symm.index_eq_card] at hc
  have hdouble := coprime_semidirect_doubling φ hcop
  have heG := cyc_eq_of_mulEquiv (SemidirectProduct.mulEquivSubgroup hH)
  have heH := cyc_eq_of_mulEquiv hH.symm.QuotientMulEquiv
  change cyc (N ⋊[φ] H) = cyc G at heG
  rw [heH, ← heG]
  exact hdouble

end CoprimeDoubling

namespace CyclicSum

noncomputable section

variable {G : Type*} [Group G] [Fintype G]

def generatorsEquiv (K : Subgroup G) :
    {x : G // Subgroup.zpowers x = K} ≃
      {x : K // orderOf x = Nat.card K} where
  toFun x := ⟨⟨x, x.2.le (Subgroup.mem_zpowers x.1)⟩, by
    rw [Subgroup.orderOf_mk, ← Nat.card_zpowers, x.2]⟩
  invFun x := ⟨x.1, by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem x.1.2)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact le_of_eq x.2.symm⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem card_generators (K : Subgroup G) [IsCyclic K] :
    Nat.card {x : G // Subgroup.zpowers x = K} = Nat.totient (Nat.card K) := by
  classical
  rw [Nat.card_congr (generatorsEquiv K), Nat.card_eq_fintype_card]
  simpa [Fintype.card_subtype, Nat.card_eq_fintype_card] using
    (IsCyclic.card_orderOf_eq_totient (α := K) (d := Fintype.card K) dvd_rfl)

abbrev CyclicSubgroups (G : Type*) [Group G] := {K : Subgroup G // IsCyclic K}

def generated (x : G) : CyclicSubgroups G := ⟨Subgroup.zpowers x, inferInstance⟩

theorem card_generated_fiber (K : CyclicSubgroups G) :
    Nat.card {x : G // generated x = K} = Nat.totient (Nat.card K.1) := by
  classical
  let : IsCyclic K.1 := K.2
  have heq : (fun x : G => generated x = K) =
      (fun x : G => Subgroup.zpowers x = K.1) := by
    funext x
    exact propext Subtype.ext_iff
  rw [heq]
  exact card_generators K.1

theorem cyclic_count_eq_sum :
    (Nat.card (CyclicSubgroups G) : ℚ) =
      ∑ x : G, (1 : ℚ) / Nat.totient (orderOf x) := by
  classical
  rw [← Fintype.sum_fiberwise (generated (G := G))]
  calc
    (Nat.card (CyclicSubgroups G) : ℚ) = ∑ _K : CyclicSubgroups G, (1 : ℚ) := by
      simp [Nat.card_eq_fintype_card]
    _ = ∑ K : CyclicSubgroups G, ∑ x : {x : G // generated x = K},
        (1 : ℚ) / Nat.totient (orderOf x.1) := by
      apply Fintype.sum_congr
      intro K
      have hx (x : {x : G // generated x = K}) : orderOf x.1 = Nat.card K.1 := by
        rw [← Nat.card_zpowers]
        exact congrArg (fun L : Subgroup G => Nat.card L) (congrArg Subtype.val x.2)
      simp_rw [hx]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, card_generated_fiber]
      have hpos : 0 < Nat.totient (Nat.card K.1) :=
        Nat.totient_pos.mpr Nat.card_pos
      field_simp

end

end CyclicSum

section Arithmetic

/-- Adding a positive power of a new prime increases the number of distinct
prime factors by exactly one. -/
theorem card_primeFactors_prime_pow_mul_of_not_dvd
    (p k n : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hn : 0 < n) (hpn : ¬p ∣ n) :
    (p ^ k * n).primeFactors.card = n.primeFactors.card + 1 := by
  have hnotmem : p ∉ n.primeFactors := by
    intro h
    exact hpn (Nat.mem_primeFactors.mp h).2.1
  rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (by omega),
    Nat.primeFactors_prime_pow (by omega) hp]
  simp [hnotmem]

/-- A positive power of an already present prime does not change the number
of distinct prime factors. -/
theorem card_primeFactors_prime_pow_mul_of_dvd
    (p k n : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hn : 0 < n) (hpn : p ∣ n) :
    (p ^ k * n).primeFactors.card = n.primeFactors.card := by
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
  rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (by omega),
    Nat.primeFactors_prime_pow (by omega) hp]
  simp [hmem]

/-- Each prime in the factorization contributes at least two divisors. -/
theorem pow_card_le_prod_factorization_succ (m : ℕ) (s : Finset ℕ)
    (hs : s ⊆ m.primeFactors) :
    2 ^ s.card ≤ ∏ p ∈ s, (m.factorization p + 1) := by
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun _ _ => by omega)
  intro p hp
  have hpm := Nat.mem_primeFactors.mp (hs hp)
  have he := hpm.1.factorization_pos_of_dvd hpm.2.2 hpm.2.1
  omega

/-- The divisor count is at least two to the number of distinct prime factors. -/
theorem two_pow_card_primeFactors_le_card_divisors (m : ℕ) (hm : 0 < m) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [Nat.card_divisors (by omega)]
  exact pow_card_le_prod_factorization_succ m m.primeFactors (Finset.Subset.refl _)

/-- A chosen prime-power divisor improves the usual divisor-count bound
by the ratio `(v_p(m)+1)/2`. The statement is cleared of denominators. -/
theorem prime_factor_divisor_count_bound (m p : ℕ) (hm : m ≠ 0)
    (hp : p ∈ m.primeFactors) :
    (m.factorization p + 1) * 2 ^ m.primeFactors.card ≤ 2 * m.divisors.card := by
  have hcard := Finset.card_erase_add_one hp
  have hprod := Finset.mul_prod_erase m.primeFactors (fun q => m.factorization q + 1) hp
  have hbase := pow_card_le_prod_factorization_succ m (m.primeFactors.erase p)
    (Finset.erase_subset _ _)
  rw [Nat.card_divisors hm, ← hprod, ← hcard, pow_succ]
  calc
    _ = 2 * ((m.factorization p + 1) * 2 ^ (m.primeFactors.erase p).card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hbase)

/-- The `a=3` arithmetic branch: this small divisor count forces squarefreeness.
Oddness is unnecessary for the conclusion. -/
theorem squarefree_of_six_mul_card_divisors_lt (m : ℕ) (hm : 0 < m)
    (hsmall : 6 * m.divisors.card < 8 * 2 ^ m.primeFactors.card) : Squarefree m := by
  apply Nat.squarefree_of_factorization_le_one (by omega)
  intro p
  by_contra he
  have he2 : 2 ≤ m.factorization p := by omega
  have hmem : p ∈ m.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by omega)
  have hb := prime_factor_divisor_count_bound m p (by omega) hmem
  have hp : 0 < 2 ^ m.primeFactors.card := by positivity
  have hge : 3 * 2 ^ m.primeFactors.card ≤
      (m.factorization p + 1) * 2 ^ m.primeFactors.card := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- Two distinct prime factors improve the divisor-count bound by the product
of their two exponent contributions, with all denominators cleared. -/
theorem two_prime_factor_divisor_count_bound (m p q : ℕ) (hm : m ≠ 0)
    (hp : p ∈ m.primeFactors) (hq : q ∈ m.primeFactors) (hpq : p ≠ q) :
    (m.factorization p + 1) * (m.factorization q + 1) * 2 ^ m.primeFactors.card ≤
      4 * m.divisors.card := by
  have hqp : q ∈ m.primeFactors.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩
  let s := (m.primeFactors.erase p).erase q
  have hcard : m.primeFactors.card = s.card + 2 := by
    have hA := Finset.card_erase_add_one hp
    have hB := Finset.card_erase_add_one hqp
    dsimp [s]
    omega
  have hbase := pow_card_le_prod_factorization_succ m s
    ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  calc
    _ = 4 * (((m.factorization p + 1) * (m.factorization q + 1)) * 2 ^ s.card) := by
      rw [hcard, pow_add]
      ring
    _ ≤ 4 * (((m.factorization p + 1) * (m.factorization q + 1)) *
        ∏ r ∈ s, (m.factorization r + 1)) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ hbase)
    _ = 4 * m.divisors.card := by
      rw [Nat.card_divisors hm,
        ← Finset.mul_prod_erase _ (fun r => m.factorization r + 1) hp,
        ← Finset.mul_prod_erase _ (fun r => m.factorization r + 1) hqp]
      dsimp [s]
      ring

/-- The `a=2` arithmetic branch: every exponent is at most two, and at most
one prime can have exponent two. Oddness is unnecessary. -/
theorem factorization_shape_of_four_mul_card_divisors_lt (m : ℕ) (hm : 0 < m)
    (hsmall : 4 * m.divisors.card < 8 * 2 ^ m.primeFactors.card) :
    (∀ p, m.factorization p ≤ 2) ∧
      ∀ p q, 2 ≤ m.factorization p → 2 ≤ m.factorization q → p = q := by
  have hmem (p : ℕ) (he : 1 ≤ m.factorization p) : p ∈ m.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by omega)
  have hpos : 0 < 2 ^ m.primeFactors.card := by positivity
  constructor
  · intro p
    by_contra he
    have he3 : 3 ≤ m.factorization p := by omega
    have hb := prime_factor_divisor_count_bound m p (by omega) (hmem p (by omega))
    have hge : 4 * 2 ^ m.primeFactors.card ≤
        (m.factorization p + 1) * 2 ^ m.primeFactors.card :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · intro p q hp hq
    by_contra hpq
    have hb := two_prime_factor_divisor_count_bound m p q (by omega)
      (hmem p (by omega)) (hmem q (by omega)) hpq
    have hcoeff : 9 ≤ (m.factorization p + 1) * (m.factorization q + 1) := by nlinarith
    have hge := Nat.mul_le_mul_right (2 ^ m.primeFactors.card) hcoeff
    omega

end Arithmetic

/-- A least-order counterexample has no nontrivial normal p-subgroup.
The smaller-group hypothesis is the well-founded induction hypothesis. -/
theorem no_normal_p_subgroup_of_minimal_counterexample
    (G : Type) [Group G] [Fintype G]
    (hns : ¬ Group.IsSolvable G) (hlt : cyc G < 2 ^ (numPrimeFactors G + 2))
    (hmin : ∀ (H : Type) [Group H] [Fintype H], Nat.card H < Nat.card G →
      ¬ Group.IsSolvable H → 2 ^ (numPrimeFactors H + 2) ≤ cyc H)
    (p : ℕ) (hp : p.Prime) (N : Subgroup G) [N.Normal] [Nontrivial N]
    (hP : IsPGroup p N) : False := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  have : Group.IsNilpotent N := hP.isNilpotent
  have hQns : ¬ Group.IsSolvable (G ⧸ N) := by
    intro h
    exact hns ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, h⟩)
  obtain ⟨k, hk, hNk⟩ := hP.nontrivial_iff_card.mp inferInstance
  have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  have hNgt : 1 < Nat.card N := Finite.one_lt_card
  have hcard : Nat.card G = p ^ k * Nat.card (G ⧸ N) := by
    rw [← N.card_mul_index, N.index_eq_card, hNk]
  have hQlt : Nat.card (G ⧸ N) < Nat.card G := by
    rw [← N.card_mul_index, N.index_eq_card]
    nlinarith
  have hbound := hmin (G ⧸ N) hQlt hQns
  by_cases hpd : p ∣ Nat.card (G ⧸ N)
  · have hω : numPrimeFactors G = numPrimeFactors (G ⧸ N) := by
      simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
      rw [hcard]
      exact card_primeFactors_prime_pow_mul_of_dvd p k _ hp hk hQpos hpd
    have hcyc := cyc_le_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    rw [hω] at hlt
    exact (Nat.not_lt_of_ge (hbound.trans hcyc)) hlt
  · have hω : numPrimeFactors G = numPrimeFactors (G ⧸ N) + 1 := by
      simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
      rw [hcard]
      exact card_primeFactors_prime_pow_mul_of_not_dvd p k _ hp hk hQpos hpd
    have hcop : (Nat.card N).Coprime N.index := by
      rw [hNk, N.index_eq_card]
      exact (hp.coprime_iff_not_dvd.mpr hpd).pow_left k
    have hdouble := normal_hall_doubling N hcop
    have hpow : 2 ^ (numPrimeFactors G + 2) =
        2 * 2 ^ (numPrimeFactors (G ⧸ N) + 2) := by
      rw [hω, show numPrimeFactors (G ⧸ N) + 1 + 2 =
        (numPrimeFactors (G ⧸ N) + 2) + 1 by omega, pow_succ, Nat.mul_comm]
    rw [hpow] at hlt
    exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_left 2 hbound).trans hdouble)) hlt

namespace RadicalFree

noncomputable section

variable {G : Type*} [Group G]

/-- A nontrivial solvable group has a last nontrivial term in its derived series. -/
theorem exists_last_derived [Nontrivial G] [Group.IsSolvable G] :
    ∃ n : ℕ, derivedSeries G n ≠ ⊥ ∧ derivedSeries G (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  induction n with
  | zero =>
      exact False.elim ((show (⊤ : Subgroup G) ≠ ⊥ from top_ne_bot) hn)
  | succ n ih =>
      by_cases h : derivedSeries G n = ⊥
      · exact ih h
      · exact ⟨n, h, hn⟩

/-- A nontrivial finite solvable group has a nontrivial characteristic p-subgroup. -/
theorem exists_characteristic_p_subgroup [Finite G] [Nontrivial G] [Group.IsSolvable G] :
    ∃ p : ℕ, p.Prime ∧ ∃ N : Subgroup G,
      N ≠ ⊥ ∧ N.Characteristic ∧ IsPGroup p N := by
  classical
  obtain ⟨n, hn, hnnext⟩ := exists_last_derived (G := G)
  let A := derivedSeries G n
  have hA : A ≠ ⊥ := hn
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  let : IsMulCommutative A := Subgroup.commutator_self_eq_bot_iff.mp hnnext
  have hcard : Nat.card A ≠ 1 := Finite.one_lt_card.ne'
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p A := Classical.choice inferInstance
  let : P.Characteristic := P.characteristic_of_normal inferInstance
  refine ⟨p, hp, (P : Subgroup A).map A.subtype, ?_, inferInstance,
    P.isPGroup'.map A.subtype⟩
  intro h
  exact P.ne_bot_of_dvd_card hpdvd
    (((P : Subgroup A).map_eq_bot_iff_of_injective A.subtype_injective).mp h)

/-- A nontrivial solvable normal subgroup supplies a nontrivial normal p-subgroup. -/
theorem exists_normal_p_subgroup_of_solvable_normal [Finite G]
    (R : Subgroup G) [R.Normal] [Group.IsSolvable R] (hR : R ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ ∃ N : Subgroup G,
      N ≠ ⊥ ∧ N.Normal ∧ IsPGroup p N := by
  classical
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR
  obtain ⟨p, hp, K, hK, hchar, hpK⟩ := exists_characteristic_p_subgroup (G := R)
  let : K.Characteristic := hchar
  refine ⟨p, hp, K.map R.subtype, ?_, inferInstance, hpK.map R.subtype⟩
  exact fun h => hK ((K.map_eq_bot_iff_of_injective R.subtype_injective).mp h)

/-- Excluding nontrivial normal p-subgroups excludes all nontrivial solvable normal subgroups. -/
theorem solvable_normal_eq_bot_of_no_normal_p_subgroup [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∀ N : Subgroup G,
      N.Normal → IsPGroup p N → N = ⊥)
    (R : Subgroup G) [R.Normal] [Group.IsSolvable R] : R = ⊥ := by
  by_contra hR
  obtain ⟨p, hp, N, hN, hn, hpN⟩ := exists_normal_p_subgroup_of_solvable_normal R hR
  exact hN (h p hp N hn hpN)

end

end RadicalFree

/-- Every solvable normal subgroup of a least-order counterexample is trivial. -/
theorem minimal_counterexample_solvable_normal_eq_bot
    (G : Type) [Group G] [Fintype G]
    (hns : ¬ Group.IsSolvable G) (hlt : cyc G < 2 ^ (numPrimeFactors G + 2))
    (hmin : ∀ (H : Type) [Group H] [Fintype H], Nat.card H < Nat.card G →
      ¬ Group.IsSolvable H → 2 ^ (numPrimeFactors H + 2) ≤ cyc H)
    (R : Subgroup G) [R.Normal] [Group.IsSolvable R] : R = ⊥ := by
  apply RadicalFree.solvable_normal_eq_bot_of_no_normal_p_subgroup
  intro p hp N hn hP
  by_contra hN
  let : N.Normal := hn
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  exact no_normal_p_subgroup_of_minimal_counterexample G hns hlt hmin p hp N hP

/-- The remaining structural case suffices for the conjecture. The hypothesis
is restricted to groups with no nontrivial solvable normal subgroup; this lemma
proves the reduction to that case and does not establish the hypothesis. -/
theorem lower_bound_of_radicalFree_case
    (hcase : ∀ (G : Type) [Group G] [Fintype G],
      (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
      ¬ Group.IsSolvable G → 2 ^ (numPrimeFactors G + 2) ≤ cyc G) :
    NonSolvableLowerBound := by
  have aux : ∀ n : ℕ, ∀ (G : Type) [Group G] [Fintype G], Nat.card G = n →
      ¬ Group.IsSolvable G → 2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G _ _ hcard hns
      by_cases hlt : cyc G < 2 ^ (numPrimeFactors G + 2)
      · have hmin : ∀ (H : Type) [Group H] [Fintype H], Nat.card H < Nat.card G →
            ¬ Group.IsSolvable H → 2 ^ (numPrimeFactors H + 2) ≤ cyc H := by
          intro H _ _ hH hnsH
          exact ih (Nat.card H) (hcard ▸ hH) H rfl hnsH
        apply hcase G ?_ hns
        intro N hn hs
        let : N.Normal := hn
        let : Group.IsSolvable N := hs
        exact minimal_counterexample_solvable_normal_eq_bot G hns hlt hmin N
      · exact Nat.le_of_not_gt hlt
  intro G _ _ hns
  exact aux (Nat.card G) G rfl hns

namespace SylowInputs

open Subgroup

theorem normalizer_le_centralizer_of_aut_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsMulCommutative P]
    (hAut : IsPGroup p (MulAut P)) :
    normalizer P ≤ centralizer (P : Set G) := by
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, ← relIndex] at key
  refine relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes ?_ dvd_rfl key)
  obtain ⟨k, hk⟩ := hAut.exists_card_eq
  rw [hk]
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_left _ P.le_centralizer)
  apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_index_of_le P.le_normalizer)
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact P.not_dvd_index

theorem exists_normal_complement_of_aut_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsMulCommutative P]
    (hAut : IsPGroup p (MulAut P)) :
    ∃ N : Subgroup G, N.Normal ∧ N.IsComplement' (P : Subgroup G) := by
  let hNC := normalizer_le_centralizer_of_aut_isPGroup P hAut
  exact ⟨(MonoidHom.transferSylow P hNC).ker, inferInstance,
    MonoidHom.ker_transferSylow_isComplement' P hNC⟩

end SylowInputs

open scoped BigOperators
namespace CyclicSum
noncomputable section

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem cyclic_count_eq_divisors_card [IsCyclic G] :
    Nat.card (CyclicSubgroups G) = (Nat.card G).divisors.card := by
  classical
  let := Fintype.ofFinite G
  have hm (x : G) (_hx : x ∈ Finset.univ) : orderOf x ∈ (Nat.card G).divisors :=
    Nat.mem_divisors.mpr ⟨orderOf_dvd_natCard x, Nat.card_pos.ne'⟩
  have hq : (Nat.card (CyclicSubgroups G) : ℚ) = (Nat.card G).divisors.card := by
    rw [cyclic_count_eq_sum, ← Finset.sum_fiberwise_of_maps_to hm]
    calc
      (∑ d ∈ (Nat.card G).divisors, ∑ x : G with orderOf x = d,
          (1 : ℚ) / Nat.totient (orderOf x)) =
          ∑ _d ∈ (Nat.card G).divisors, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hconst : (∑ x : G with orderOf x = d, (1 : ℚ) / Nat.totient (orderOf x)) =
            ∑ _x : G with orderOf _x = d, (1 : ℚ) / Nat.totient d := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        rw [hconst, Finset.sum_const, nsmul_eq_mul,
          IsCyclic.card_orderOf_eq_totient (by simpa [Nat.card_eq_fintype_card] using
            (Nat.mem_divisors.mp hd).1)]
        have hpos : 0 < Nat.totient d := Nat.totient_pos.mpr
          (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 Nat.card_pos)
        field_simp
      _ = _ := by simp
  exact_mod_cast hq

end
end CyclicSum

namespace TwoFactor
noncomputable section

end
end TwoFactor

namespace ComparisonModel
open TwoFactor
noncomputable section

end
end ComparisonModel

namespace ElementaryCollapse
open TwoFactor
noncomputable section

end
end ElementaryCollapse

namespace CyclicSum

end CyclicSum

namespace ElementaryBound
open TwoFactor
noncomputable section

end
end ElementaryBound

namespace Conjecture55C4C2

abbrev A := ZMod 4 × ZMod 2

open Subgroup

end Conjecture55C4C2

namespace OrderShape

end OrderShape

namespace PrimePower

end PrimePower

namespace AlternatingSeven

end AlternatingSeven

/-- Conditional bridge to the requested affirmative FC statement.
Its hypothesis is equivalent to the full conjecture, not a solved input. -/
theorem affirmative_target_of_lower_bound (h : NonSolvableLowerBound) :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G := by
  constructor
  · intro _
    exact conjecture55_iff_lower_bound.mpr h
  · intro _
    trivial

-- Audit the foundational components.

end

end Conjecture55Lean4Web
end

/-! ### Module `RootWeights` -/
section
/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

/-!
# Cyclic subgroup counts as weighted root counts

The weights come from fibers in the unit group modulo a common exponent.
They are nonnegative, and root-count comparisons imply cyclic-count comparisons.
-/

open scoped BigOperators

namespace RootWeights
noncomputable section

def rootDivisor (n : ℕ) (u : (ZMod n)ˣ) : ℕ :=
  Nat.gcd n (((u : ZMod n) - 1).val)

theorem rootDivisor_dvd (n : ℕ) (u : (ZMod n)ˣ) : rootDivisor n u ∣ n :=
  Nat.gcd_dvd_left _ _

theorem dvd_rootDivisor_iff_unitsMap_eq_one {n r : ℕ} [NeZero n]
    (hr : r ∣ n) (u : (ZMod n)ˣ) :
    r ∣ rootDivisor n u ↔ ZMod.unitsMap hr u = 1 := by
  have hcast : ((((u : ZMod n) - 1).val : ℕ) : ZMod r) =
      (ZMod.castHom hr (ZMod r)) (u : ZMod n) - 1 := by
    have h := congrArg (ZMod.castHom hr (ZMod r))
      (ZMod.natCast_zmod_val ((u : ZMod n) - 1))
    simpa only [map_natCast, map_sub, map_one] using h
  rw [rootDivisor, Nat.dvd_gcd_iff, and_iff_right hr,
    ← ZMod.natCast_eq_zero_iff, hcast, sub_eq_zero]
  change ((ZMod.unitsMap hr u : ZMod r) = (1 : (ZMod r)ˣ)) ↔ _
  exact Units.ext_iff.symm

theorem card_kernel_unitsMap_mul_totient {n r : ℕ} [NeZero n]
    (hr : r ∣ n) :
    Nat.card (ZMod.unitsMap hr).ker * r.totient = n.totient := by
  have : NeZero r := ⟨fun hz => (NeZero.ne n) (Nat.eq_zero_of_zero_dvd (hz ▸ hr))⟩
  have hs := ZMod.unitsMap_surjective hr
  have hc := (ZMod.unitsMap hr).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs, Subgroup.card_top] at hc
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using hc

def rootKernelEquiv {n r : ℕ} [NeZero n] (hr : r ∣ n) :
    {u : (ZMod n)ˣ // r ∣ rootDivisor n u} ≃ (ZMod.unitsMap hr).ker :=
  Equiv.subtypeEquivRight (fun u => dvd_rootDivisor_iff_unitsMap_eq_one hr u)

theorem reciprocal_totient_eq_unit_average {n r : ℕ} [NeZero n]
    (hr : r ∣ n) :
    (1 : ℚ) / r.totient =
      (∑ u : (ZMod n)ˣ, if r ∣ rootDivisor n u then (1 : ℚ) else 0) / n.totient := by
  classical
  have hs : (∑ u : (ZMod n)ˣ, if r ∣ rootDivisor n u then (1 : ℚ) else 0) =
      (Nat.card (ZMod.unitsMap hr).ker : ℚ) := by
    rw [← Nat.card_congr (rootKernelEquiv hr)]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hs]
  have hc : (Nat.card (ZMod.unitsMap hr).ker : ℚ) * r.totient = n.totient := by
    exact_mod_cast card_kernel_unitsMap_mul_totient hr
  have hn : (n.totient : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  have hr0 : (r.totient : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hr (NeZero.pos n))).ne'
  field_simp
  simpa [mul_comm] using hc.symm

theorem cyclic_count_eq_unit_average
    {G : Type*} [Group G] [Fintype G] {n : ℕ} [NeZero n]
    (hG : ∀ x : G, orderOf x ∣ n) :
    (Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) : ℚ) =
      (∑ u : (ZMod n)ˣ, (Nat.card {x : G // x ^ (rootDivisor n u) = 1} : ℚ)) /
        n.totient := by
  classical
  rw [Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_sum]
  simp_rw [reciprocal_totient_eq_unit_average (hG _)]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [orderOf_dvd_iff_pow_eq_one]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

end
end RootWeights
end

/-! ### Module `Period` -/
section
namespace Conjecture55FrobeniusProof
open Function

theorem dvd_card_of_all_minimalPeriod_eq {X : Type*} [Fintype X]
    (f : Equiv.Perm X) (m : ℕ) (hm : ∀ x, minimalPeriod f x = m) :
    m ∣ Fintype.card X := by
  classical
  let C := Subgroup.zpowers f
  let Ω := Quotient (MulAction.orbitRel C X)
  have hc (x : X) : Fintype.card (MulAction.orbit C x) = m := by
    rw [← MulAction.minimalPeriod_eq_card f x]
    exact hm x
  rw [Fintype.card_congr (MulAction.selfEquivSigmaOrbits C X), Fintype.card_sigma]
  exact Finset.dvd_sum fun ω _ => by rw [hc]

theorem dvd_card_periodicPts_of_minimal {X : Type*} [Fintype X] [DecidableEq X]
    (f : Equiv.Perm X) {m : ℕ} (hm : 0 < m)
    (hmin : ∀ x, m ≤ minimalPeriod f x) :
    m ∣ Fintype.card {x : X // IsPeriodicPt f m x} := by
  classical
  have hi (x : X) : IsPeriodicPt f m (f x) ↔ IsPeriodicPt f m x := by
    constructor
    · intro h
      apply f.injective
      simpa only [IsPeriodicPt, IsFixedPt, Function.iterate_succ_apply,
        ← Function.iterate_succ_apply'] using h
    · exact IsPeriodicPt.apply
  let e := f.subtypePerm hi
  apply dvd_card_of_all_minimalPeriod_eq e m
  intro x
  have he : minimalPeriod e x = minimalPeriod f x.val := by
    apply minimalPeriod_eq_minimalPeriod_iff.mpr
    intro k
    have hh : ∀ y : {x : X // IsPeriodicPt f m x},
        ((e : _ → _)^[k] y).val = (f : X → X)^[k] y.val := by
      intro y
      induction k with
      | zero => rfl
      | succ k ih =>
        simpa only [Function.iterate_succ_apply', e, Equiv.Perm.subtypePerm_apply] using
          congrArg f ih
    change ((e : _ → _)^[k] x = x) ↔ _
    rw [Subtype.ext_iff, hh]
    rfl
  rw [he]
  exact Nat.le_antisymm (x.prop.minimalPeriod_le hm) (hmin x.val)

theorem exists_periodic_card_of_fixed_card_dvd {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (f : Equiv.Perm X)
    (hcard : ∀ k, (∃ x, IsPeriodicPt f k x) →
      Fintype.card {x : X // IsPeriodicPt f k x} ∣ Fintype.card X) :
    ∃ x, IsPeriodicPt f (Fintype.card X) x := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_min_image Finset.univ
    (fun x => minimalPeriod f x) Finset.univ_nonempty
  have hp : 0 < minimalPeriod f x :=
    minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts x)
  have hd := dvd_card_periodicPts_of_minimal f hp (fun y => hx y (Finset.mem_univ y))
  have he := isPeriodicPt_minimalPeriod f x
  exact ⟨x, he.trans_dvd (hd.trans (hcard _ ⟨x, he⟩))⟩

end Conjecture55FrobeniusProof
end

/-! ### Module `Affine` -/
section
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

end Conjecture55FrobeniusProof
end

/-! ### Module `Brauer` -/
section
namespace Conjecture55FrobeniusProof
open Function
variable {G : Type*} [Group G]

theorem affine_conj_iterate (U : Subgroup G) [U.Normal] (v : G) (u a : U) (k : ℕ) :
    (((affinePerm (MulAut.conjNormal v⁻¹) u : U → U)^[k]) a : G) =
      (v ^ k)⁻¹ * (a : G) * (v * (u : G)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', affinePerm_apply, Subgroup.coe_mul,
      MulAut.conjNormal_apply, inv_inv, ih, pow_succ, pow_succ, mul_inv_rev]
    group

/-- Brauer's finite-normal-subgroup power-conjugacy lemma. -/
theorem brauer_power_conjugacy (U : Subgroup G) [U.Normal] [Fintype U]
    (v : G) (u : U) :
    ∃ a : U, (a : G)⁻¹ * v ^ Fintype.card U * a =
      (v * (u : G)) ^ Fintype.card U := by
  classical
  obtain ⟨a, ha⟩ := exists_affine_periodic_card (MulAut.conjNormal v⁻¹) u
  have h := congrArg (fun a : U => (a : G)) ha
  rw [affine_conj_iterate] at h
  refine ⟨a, ?_⟩
  have hh := congrArg (fun z : G => (a : G)⁻¹ * v ^ Fintype.card U * z) h
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left] using hh.symm

theorem pow_mul_eq_one_of_normal_card_dvd (U : Subgroup G) [U.Normal] [Fintype U]
    {n : ℕ} (hn : Fintype.card U ∣ n) (v : G) (hv : v ^ n = 1) (u : U) :
    (v * (u : G)) ^ n = 1 := by
  obtain ⟨a, ha⟩ := brauer_power_conjugacy U v u
  have hc : IsConj (v ^ Fintype.card U) ((v * (u : G)) ^ Fintype.card U) :=
    isConj_iff.mpr ⟨(a : G)⁻¹, by simpa using ha⟩
  obtain ⟨k, hk⟩ := hn
  have hp := hc.pow k
  rw [← pow_mul, ← pow_mul, ← hk, hv] at hp
  exact isConj_one_right.mp hp

end Conjecture55FrobeniusProof
end

/-! ### Module `CountFibers` -/
section
namespace Conjecture55FrobeniusProof

noncomputable def sigmaStabilizerEquivOrbitProd {H T : Type*} [Group H] [MulAction H T] :
    (Σ t : T, MulAction.stabilizer H t) ≃
      (Quotient (MulAction.orbitRel H T)) × H :=
  (show (Σ t : T, MulAction.stabilizer H t) ≃
      (Σ h : H, MulAction.fixedBy T h) from {
    toFun := fun ⟨t, h⟩ => ⟨h.val, ⟨t, h.prop⟩⟩
    invFun := fun ⟨h, t⟩ => ⟨t.val, ⟨h, t.prop⟩⟩
    left_inv := by rintro ⟨t, ⟨h, hh⟩⟩; rfl
    right_inv := by rintro ⟨h, ⟨t, ht⟩⟩; rfl
  }).trans (MulAction.sigmaFixedByEquivOrbitsProdGroup H T)

theorem group_card_dvd_card_of_fiber_equiv_stabilizer
    {H S T : Type*} [Group H] [Fintype H] [Fintype S] [Fintype T] [MulAction H T]
    (f : S → T) (e : ∀ t, {s : S // f s = t} ≃ MulAction.stabilizer H t) :
    Fintype.card H ∣ Fintype.card S := by
  classical
  let E := ((Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight e)).trans sigmaStabilizerEquivOrbitProd
  rw [Fintype.card_congr E, Fintype.card_prod]
  exact dvd_mul_left _ _

end Conjecture55FrobeniusProof
end

/-! ### Module `TailCore` -/
section
noncomputable section
namespace Conjecture55FrobeniusProof
open Function
variable {G : Type*} [Group G]

def powerTail (H : Subgroup G) (x : G) : ℤ → G ⧸ H := fun k => ↑(x ^ k)

def powerCore (H : Subgroup G) (x : G) : Subgroup G where
  carrier := {h | ∀ k : ℤ, (x ^ k)⁻¹ * h * x ^ k ∈ H}
  one_mem' := by intro k; simpa using H.one_mem
  mul_mem' := by
    intro a b ha hb k
    have ht := H.mul_mem (ha k) (hb k)
    convert ht using 1 <;> group
  inv_mem' := by
    intro a ha k
    have ht := H.inv_mem (ha k)
    convert ht using 1 <;> group

theorem powerCore_le (H : Subgroup G) (x : G) : powerCore H x ≤ H := by
  intro h hh
  simpa using hh 0

theorem mem_normalizer_powerCore (H : Subgroup G) (x : G) :
    x ∈ Subgroup.normalizer (powerCore H x : Set G) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro h
  constructor
  · intro hh k
    have ht := hh (k - 1)
    convert ht using 1 <;> simp only [zpow_sub, zpow_one] <;> group
  · intro hh k
    have ht := hh (k + 1)
    convert ht using 1 <;> simp only [zpow_add, zpow_one] <;> group

theorem tail_eq_implies_core (H : Subgroup G) (x y : G)
    (hxy : powerTail H x = powerTail H y) :
    x⁻¹ * y ∈ powerCore H x := by
  intro k
  have hk : (y ^ k)⁻¹ * x ^ k ∈ H :=
    QuotientGroup.eq.mp ((congrFun hxy k).symm)
  have hk1 : (x ^ (k + 1))⁻¹ * y ^ (k + 1) ∈ H :=
    QuotientGroup.eq.mp (congrFun hxy (k + 1))
  have ht := H.mul_mem hk1 hk
  convert ht using 1 <;> simp only [zpow_add, zpow_one] <;> group

theorem tail_conj (H : Subgroup G) (h : H) (x : G) :
    powerTail H ((h : G) * x * (h : G)⁻¹) = h • powerTail H x := by
  funext k
  change (↑(((h : G) * x * (h : G)⁻¹) ^ k) : G ⧸ H) = ↑((h : G) * x ^ k)
  rw [conj_zpow]
  exact QuotientGroup.mk_mul_of_mem _ (H.inv_mem h.prop)

theorem pow_mul_eq_one_of_mem_normalizer (U : Subgroup G) [Finite U]
    {n : ℕ} (hn : Nat.card U ∣ n) (v : G) (hv : v ^ n = 1)
    (hvU : v ∈ Subgroup.normalizer (U : Set G)) (u : U) :
    (v * (u : G)) ^ n = 1 := by
  classical
  let V := Subgroup.normalizer (U : Set G)
  let W : Subgroup V := U.subgroupOf V
  let v' : V := ⟨v, hvU⟩
  let u' : W := ⟨⟨u.val, U.le_normalizer u.prop⟩, u.prop⟩
  letI : Finite W := Finite.of_equiv U
    (Subgroup.subgroupOfEquivOfLe U.le_normalizer).toEquiv.symm
  letI := Fintype.ofFinite W
  have hwcard : Fintype.card W = Nat.card U := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe U.le_normalizer).toEquiv
  have hv' : v' ^ n = 1 := Subtype.ext hv
  have ht := pow_mul_eq_one_of_normal_card_dvd W (hwcard ▸ hn) v' hv' u'
  exact congrArg (fun z : V => (z : G)) ht

theorem tail_mul_core (H : Subgroup G) (x : G) (h : powerCore H x) :
    powerTail H (x * (h : G)) = powerTail H x := by
  let U := powerCore H x
  let V := Subgroup.normalizer (U : Set G)
  let W : Subgroup V := U.subgroupOf V
  let x' : V := ⟨x, mem_normalizer_powerCore H x⟩
  let h' : V := ⟨h.val, U.le_normalizer h.prop⟩
  have hh' : QuotientGroup.mk' W h' = 1 := by
    exact (QuotientGroup.eq_one_iff h').mpr (show h' ∈ W from h.prop)
  funext k
  have he : QuotientGroup.mk' W ((x' * h') ^ k) = QuotientGroup.mk' W (x' ^ k) := by
    simp only [map_zpow, map_mul, hh', mul_one]
  have hm : (((x' * h') ^ k)⁻¹ * x' ^ k) ∈ W := QuotientGroup.eq.mp he
  apply QuotientGroup.eq.mpr
  exact powerCore_le H x hm

theorem tail_eq_iff_core (H : Subgroup G) (x y : G) :
    powerTail H x = powerTail H y ↔ x⁻¹ * y ∈ powerCore H x := by
  constructor
  · exact tail_eq_implies_core H x y
  · intro h
    have ht := tail_mul_core H x ⟨x⁻¹ * y, h⟩
    simpa only [mul_inv_cancel_left] using ht.symm

end Conjecture55FrobeniusProof
end
end

/-! ### Module `TailFibers` -/
section
noncomputable section
namespace Conjecture55FrobeniusProof
open Function
variable {G : Type*} [Group G]

abbrev Roots (G : Type*) [Group G] (n : ℕ) := {x : G // x ^ n = 1}
def RootTails (H : Subgroup G) (n : ℕ) := Set.range (fun x : Roots G n => powerTail H x.val)
def rootTailMap (H : Subgroup G) (n : ℕ) (x : Roots G n) : RootTails H n :=
  ⟨powerTail H x.val, ⟨x, rfl⟩⟩

instance rootTailsMulAction (H : Subgroup G) (n : ℕ) : MulAction H (RootTails H n) where
  smul h t := ⟨h • t.val, by
    obtain ⟨x, hx⟩ := t.prop
    let y : Roots G n := ⟨(h : G) * x.val * (h : G)⁻¹, by
      rw [conj_pow, x.prop]; simp⟩
    refine ⟨y, ?_⟩
    change powerTail H ((h : G) * x.val * (h : G)⁻¹) = h • t.val
    rw [tail_conj]
    exact congrArg (fun z => h • z) hx⟩
  one_smul t := Subtype.ext (one_smul H t.val)
  mul_smul h₁ h₂ t := Subtype.ext (mul_smul h₁ h₂ t.val)

def coreStabilizerEquiv (H : Subgroup G) (n : ℕ) (x : Roots G n) :
    powerCore H x.val ≃ MulAction.stabilizer H (rootTailMap H n x) where
  toFun u := ⟨⟨u.val, powerCore_le H x.val u.prop⟩, by
    apply Subtype.ext
    funext k
    change (↑(u.val * x.val ^ k) : G ⧸ H) = ↑(x.val ^ k)
    symm
    apply QuotientGroup.eq.mpr
    simpa only [mul_assoc] using u.prop k⟩
  invFun h := ⟨h.val.val, by
    intro k
    have ht := congrArg (fun t : RootTails H n => t.val k) h.prop
    change (↑(h.val.val * x.val ^ k) : G ⧸ H) = ↑(x.val ^ k) at ht
    simpa only [mul_assoc] using QuotientGroup.eq.mp ht.symm⟩
  left_inv u := by apply Subtype.ext; rfl
  right_inv h := by apply Subtype.ext; apply Subtype.ext; rfl

def rootFiberCoreEquiv [Finite G] (H : Subgroup G) (n : ℕ)
    (hn : Nat.card H ∣ n) (x : Roots G n) :
    {y : Roots G n // powerTail H y.val = powerTail H x.val} ≃ powerCore H x.val where
  toFun y := ⟨x.val⁻¹ * y.val.val, (tail_eq_iff_core H x.val y.val.val).mp y.prop.symm⟩
  invFun u := ⟨⟨x.val * u.val,
    pow_mul_eq_one_of_mem_normalizer (powerCore H x.val)
      ((Subgroup.card_dvd_of_le (powerCore_le H x.val)).trans hn)
      x.val x.prop (mem_normalizer_powerCore H x.val) u⟩,
    tail_mul_core H x.val u⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv u := by apply Subtype.ext; simp

def rootTailFiberEquiv [Finite G] (H : Subgroup G) (n : ℕ)
    (hn : Nat.card H ∣ n) (t : RootTails H n) :
    {x : Roots G n // rootTailMap H n x = t} ≃ MulAction.stabilizer H t := by
  let x := Classical.choose t.prop
  have hx := Classical.choose_spec t.prop
  have he : rootTailMap H n x = t := Subtype.ext hx
  have E : {y : Roots G n // rootTailMap H n y = rootTailMap H n x} ≃
      MulAction.stabilizer H (rootTailMap H n x) :=
    (Equiv.subtypeEquivRight (fun y => Subtype.ext_iff)).trans
      ((rootFiberCoreEquiv H n hn x).trans (coreStabilizerEquiv H n x))
  exact he ▸ E

theorem subgroup_card_dvd_root_card [Finite G] (H : Subgroup G) (n : ℕ)
    (hn : Nat.card H ∣ n) : Nat.card H ∣ Nat.card (Roots G n) := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite H
  letI : Fintype (Roots G n) := inferInstanceAs (Fintype {x : G // x ^ n = 1})
  letI : Finite (RootTails H n) := inferInstanceAs
    (Finite (Set.range (fun x : Roots G n => powerTail H x.val)))
  letI := Fintype.ofFinite (RootTails H n)
  simpa only [Nat.card_eq_fintype_card] using
    group_card_dvd_card_of_fiber_equiv_stabilizer (H := H)
      (rootTailMap H n) (rootTailFiberEquiv H n hn)

end Conjecture55FrobeniusProof
end
end

/-! ### Module `Frobenius` -/
section
namespace Conjecture55FrobeniusProof
universe u

/-- Frobenius root-count divisibility for arbitrary finite groups. -/
theorem frobenius_root_divisibility (G : Type u) [Group G] [Finite G]
    (n : ℕ) (hn : n ∣ Nat.card G) :
    n ∣ Nat.card {x : G // x ^ n = 1} := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (hpk.trans hn)
  have ht := subgroup_card_dvd_root_card H n (hH.symm ▸ hpk)
  simpa only [hH, Roots] using ht

end Conjecture55FrobeniusProof
end

/-! ### Module `PrimePowerRoots` -/
section
/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

/-!
Elementary root-count lemmas for groups containing a noncyclic prime-power subgroup.
No root-count divisibility theorem or order-divisibility bijection is assumed.
-/

namespace AmiriNext

theorem pow_eq_one_of_prime_power_card_not_cyclic
    {K : Type*} [Group K] [Finite K] {p j : ℕ} (hp : p.Prime)
    (hcard : Nat.card K = p ^ (j + 1)) (hnc : ¬ IsCyclic K) (x : K) :
    x ^ (p ^ j) = 1 := by
  have hd : orderOf x ∣ p ^ (j + 1) := hcard ▸ orderOf_dvd_natCard x
  obtain ⟨k, hkj, hk⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hne : k ≠ j + 1 := by
    intro heq
    apply hnc
    exact isCyclic_of_orderOf_eq_card x (by simpa [heq, hcard] using hk)
  exact orderOf_dvd_iff_pow_eq_one.mp (hk ▸ pow_dvd_pow p (by omega))

end AmiriNext
end

/-! ### Module `FrobeniusBridge` -/
section
/-! The precise additional root theorems needed to replace the comparison bijection.
The Frobenius divisibility and exact-root subgroup assertions remain explicit inputs. -/
namespace Conjecture55Frobenius
universe u

def RootDivisibilityInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], ∀ n : ℕ, n ∣ Nat.card G →
    n ∣ Nat.card {x : G // x ^ n = 1}

/-- The ordinary Frobenius lower bound follows from its divisibility statement. -/
theorem root_lower_bound_of_divisibility
    (hdiv : RootDivisibilityInput.{u})
    {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : n ∣ Nat.card G) :
    n ≤ Nat.card {x : G // x ^ n = 1} := by
  let : Nonempty {x : G // x ^ n = 1} := ⟨⟨1, one_pow n⟩⟩
  exact Nat.le_of_dvd Nat.card_pos (hdiv G n hn)

end Conjecture55Frobenius
end

/-! ### Module `RootDivisibilityInput` -/
section
namespace Conjecture55FrobeniusProof
universe u

/-- Discharges the precise universal input used by the existing root assembly. -/
theorem provedRootDivisibilityInput : Conjecture55Frobenius.RootDivisibilityInput.{u} :=
  frobenius_root_divisibility

theorem rootCountLowerBound (G : Type u) [Group G] [Finite G] (n : ℕ)
    (hn : n ∣ Nat.card G) : n ≤ Nat.card {x : G // x ^ n = 1} :=
  Conjecture55Frobenius.root_lower_bound_of_divisibility
    provedRootDivisibilityInput n hn

end Conjecture55FrobeniusProof
end

/-! ### Module `ComparisonRoots` -/
section
/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

/-!
# Numerical cyclic-count bounds from root estimates

Ordinary and enhanced root lower bounds remain explicit hypotheses.
The comparison requires no order-divisibility bijection.
-/

open scoped BigOperators

namespace RootWeights
noncomputable section

-- The following three elementary count lemmas reuse the checked TwoFactor proof.
theorem card_roots_cyclic {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] (d : ℕ) :
    Nat.card {x : G // x ^ d = 1} = (Nat.card G).gcd d := by
  exact IsCyclic.card_powMonoidHom_ker G d

end
end RootWeights
end

/-! ### Module `PartialCyclicCount` -/
section
/-! Partial cyclic-subgroup counts from ordinary Frobenius divisibility. -/

open scoped BigOperators

namespace Conjecture55PartialCount
open Conjecture55Lean4Web.CyclicSum
noncomputable section
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [Fintype G]

/-- Cyclic subgroups whose order divides the specified integer. -/
abbrev CyclicDividing (G : Type*) [Group G] (n : ℕ) :=
  {K : CyclicSubgroups G // Nat.card K.1 ∣ n}

def generatedRoot {n : ℕ} (x : {x : G // x ^ n = 1}) : CyclicDividing G n :=
  ⟨generated x.1, by
    change Nat.card (Subgroup.zpowers x.1) ∣ n
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one x.2⟩

def generatorFiberEquiv {n : ℕ} (K : CyclicDividing G n) :
    {x : {x : G // x ^ n = 1} // generatedRoot x = K} ≃
      {x : G // generated x = K.1} where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  invFun x := ⟨⟨x.1, by
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h := congrArg (fun L : CyclicSubgroups G => Nat.card L.1) x.2
    change Nat.card (Subgroup.zpowers x.1) = Nat.card K.1.1 at h
    rw [Nat.card_zpowers] at h
    exact h ▸ K.2⟩, Subtype.ext x.2⟩
  left_inv _x := Subtype.ext (Subtype.ext rfl)
  right_inv _x := Subtype.ext rfl

theorem card_generatedRoot_fiber {n : ℕ} (K : CyclicDividing G n) :
    Nat.card {x : {x : G // x ^ n = 1} // generatedRoot x = K} =
      (Nat.card K.1.1).totient := by
  rw [Nat.card_congr (generatorFiberEquiv K), card_generated_fiber]

theorem cyclicDividing_count_eq_sum (n : ℕ) :
    (Nat.card (CyclicDividing G n) : ℚ) =
      ∑ x : {x : G // x ^ n = 1}, (1 : ℚ) / (orderOf x.1).totient := by
  classical
  rw [← Fintype.sum_fiberwise (generatedRoot (G := G) (n := n))]
  calc
    (Nat.card (CyclicDividing G n) : ℚ) = ∑ _K : CyclicDividing G n, (1 : ℚ) := by
      simp [Nat.card_eq_fintype_card]
    _ = ∑ K : CyclicDividing G n,
        ∑ x : {x : {x : G // x ^ n = 1} // generatedRoot x = K},
          (1 : ℚ) / (orderOf x.1.1).totient := by
      apply Fintype.sum_congr
      intro K
      have hx (x : {x : {x : G // x ^ n = 1} // generatedRoot x = K}) :
          orderOf x.1.1 = Nat.card K.1.1 := by
        have h := congrArg (fun L : CyclicDividing G n => Nat.card L.1.1) x.2
        simpa only [generatedRoot, generated, Nat.card_zpowers] using h
      simp_rw [hx]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, card_generatedRoot_fiber]
      have hpos : 0 < (Nat.card K.1.1).totient := Nat.totient_pos.mpr Nat.card_pos
      field_simp

def nestedRootsEquiv {n d : ℕ} (hd : d ∣ n) :
    {x : {x : G // x ^ n = 1} // x.1 ^ d = 1} ≃ {x : G // x ^ d = 1} where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_of_pow_eq_one x.2).trans hd)⟩, x.2⟩
  left_inv _x := Subtype.ext (Subtype.ext rfl)
  right_inv _x := Subtype.ext rfl

theorem cyclicDividing_count_eq_unit_average (n : ℕ) [NeZero n] :
    (Nat.card (CyclicDividing G n) : ℚ) =
      (∑ u : (ZMod n)ˣ,
        (Nat.card {x : G // x ^ RootWeights.rootDivisor n u = 1} : ℚ)) / n.totient := by
  classical
  rw [cyclicDividing_count_eq_sum]
  have hav (x : {x : G // x ^ n = 1}) :=
    RootWeights.reciprocal_totient_eq_unit_average
      (n := n) (orderOf_dvd_of_pow_eq_one x.2)
  simp_rw [hav]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [orderOf_dvd_iff_pow_eq_one]
  rw [← Nat.card_congr (nestedRootsEquiv (G := G) (RootWeights.rootDivisor_dvd n u))]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Ordinary Frobenius root divisibility already suffices for this partial
cyclic-subgroup count; no exact-root subgroup theorem is assumed. -/
theorem divisors_card_le_cyclicDividing {n : ℕ} (hn : n ∣ Nat.card G) :
    n.divisors.card ≤ Nat.card (CyclicDividing G n) := by
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hn Nat.card_pos
  let : NeZero n := ⟨hnpos.ne'⟩
  let H := Multiplicative (ZMod n)
  have hH : ∀ x : H, orderOf x ∣ n := by
    intro x
    simpa [H] using orderOf_dvd_natCard x
  have hq : (Nat.card (CyclicSubgroups H) : ℚ) ≤
      (Nat.card (CyclicDividing G n) : ℚ) := by
    rw [RootWeights.cyclic_count_eq_unit_average hH, cyclicDividing_count_eq_unit_average]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro u _
    have hd := RootWeights.rootDivisor_dvd n u
    rw [RootWeights.card_roots_cyclic]
    simp only [H, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card, Nat.gcd_eq_right hd]
    exact Nat.cast_le.mpr (by simpa only [Nat.card_eq_fintype_card] using
      Conjecture55FrobeniusProof.rootCountLowerBound G _ (hd.trans hn))
  rw [cyclic_count_eq_divisors_card] at hq
  simpa [H] using (show (Nat.card H).divisors.card ≤
    Nat.card (CyclicDividing G n) from by exact_mod_cast hq)

end
end Conjecture55PartialCount
end

/-! ### Module `CyclicSum` -/
section
open scoped BigOperators

namespace CyclicSum

noncomputable section

variable {G : Type*} [Group G] [Fintype G]

def generatorsEquiv (K : Subgroup G) :
    {x : G // Subgroup.zpowers x = K} ≃
      {x : K // orderOf x = Nat.card K} where
  toFun x := ⟨⟨x, x.2.le (Subgroup.mem_zpowers x.1)⟩, by
    rw [Subgroup.orderOf_mk, ← Nat.card_zpowers, x.2]⟩
  invFun x := ⟨x.1, by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem x.1.2)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact le_of_eq x.2.symm⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem card_generators (K : Subgroup G) [IsCyclic K] :
    Nat.card {x : G // Subgroup.zpowers x = K} = Nat.totient (Nat.card K) := by
  classical
  rw [Nat.card_congr (generatorsEquiv K), Nat.card_eq_fintype_card]
  simpa [Fintype.card_subtype, Nat.card_eq_fintype_card] using
    (IsCyclic.card_orderOf_eq_totient (α := K) (d := Fintype.card K) dvd_rfl)

abbrev CyclicSubgroups (G : Type*) [Group G] := {K : Subgroup G // IsCyclic K}

def generated (x : G) : CyclicSubgroups G := ⟨Subgroup.zpowers x, inferInstance⟩

theorem card_generated_fiber (K : CyclicSubgroups G) :
    Nat.card {x : G // generated x = K} = Nat.totient (Nat.card K.1) := by
  classical
  let : IsCyclic K.1 := K.2
  have heq : (fun x : G => generated x = K) =
      (fun x : G => Subgroup.zpowers x = K.1) := by
    funext x
    exact propext Subtype.ext_iff
  rw [heq]
  exact card_generators K.1

theorem cyclic_count_eq_sum :
    (Nat.card (CyclicSubgroups G) : ℚ) =
      ∑ x : G, (1 : ℚ) / Nat.totient (orderOf x) := by
  classical
  rw [← Fintype.sum_fiberwise (generated (G := G))]
  calc
    (Nat.card (CyclicSubgroups G) : ℚ) = ∑ _K : CyclicSubgroups G, (1 : ℚ) := by
      simp [Nat.card_eq_fintype_card]
    _ = ∑ K : CyclicSubgroups G, ∑ x : {x : G // generated x = K},
        (1 : ℚ) / Nat.totient (orderOf x.1) := by
      apply Fintype.sum_congr
      intro K
      have hx (x : {x : G // generated x = K}) : orderOf x.1 = Nat.card K.1 := by
        rw [← Nat.card_zpowers]
        exact congrArg (fun L : Subgroup G => Nat.card L) (congrArg Subtype.val x.2)
      simp_rw [hx]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, card_generated_fiber]
      have hpos : 0 < Nat.totient (Nat.card K.1) :=
        Nat.totient_pos.mpr Nat.card_pos
      field_simp

end

end CyclicSum
end

/-! ### Module `Families` -/
section
/-!
The proof of `conjugate_family_card` is adapted from the Apache-2.0-licensed
Qiuzhen-CFSG/CFSG project, commit 96b2a02085dc678f3e0a97b334c31ada599c55fd,
GorensteinWalter/Section4/SecondCasePSL2OrderPSubgroupCount.lean, lines 24–79.
The subsequent disjoint-family counting argument is new.
-/
noncomputable section
namespace CyclicSum

theorem conjugate_family_card
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) :
    Nat.card {T : Subgroup G // ∃ g : G,
      T = U.map (MulAut.conj g).toMonoidHom} =
      (Subgroup.normalizer (U : Set G)).index := by
  classical
  let : MulAction G (Subgroup G) :=
    { smul := fun g H => H.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro H
        change H.map (MulAut.conj (1 : G)).toMonoidHom = H
        apply Subgroup.ext
        intro x
        rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
          ext x; simp]
        simp
      mul_smul := by
        intro g h H
        change H.map (MulAut.conj (g * h)).toMonoidHom =
          (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have horbit :
      MulAction.orbit G U =
        {T : Subgroup G | ∃ g : G,
          T = U.map (MulAut.conj g).toMonoidHom} := by
    ext T
    constructor
    · intro hT
      rcases hT with ⟨g, rfl⟩
      exact ⟨g, by change U.map _ = _; rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, by change U.map _ = _; rfl⟩
  have hstab : MulAction.stabilizer G U =
      Subgroup.normalizer (U : Set G) := by
    ext g
    change g • U = U ↔ g ∈ Subgroup.normalizer (U : Set G)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer U),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
            MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  change Nat.card ↥{T : Subgroup G | ∃ g : G,
    T = U.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer G U, hstab]

abbrev ConjugateFamily {G : Type*} [Group G] (U : Subgroup G) :=
  {T : Subgroup G // ∃ g : G, T = U.map (MulAut.conj g).toMonoidHom}

variable {G : Type*} [Group G] [Finite G]

theorem conjugate_family_subgroup_card (U : Subgroup G) (T : ConjugateFamily U) :
    Nat.card T.1 = Nat.card U := by
  rcases T.2 with ⟨g, hg⟩
  rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]

end CyclicSum
end
end

/-! ### Module `CyclicExtensions` -/
section
/-! Commuting coprime cyclic factors and recovery of the two factors. -/

namespace Conjecture55CyclicExtensions
noncomputable section
variable {G : Type*} [Group G] [Finite G]

theorem cyclic_subgroup_eq_of_card_eq [IsCyclic G]
    (A B : Subgroup G) (hc : Nat.card A = Nat.card B) : A = B := by
  let : CommGroup G := IsCyclic.commGroup
  have hker (A : Subgroup G) : A = (powMonoidHom (Nat.card A) : G →* G).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      change x ^ Nat.card A = 1
      exact congrArg (fun y : A => (y : G))
        (orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard (⟨x, hx⟩ : A)))
    · rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right A.card_subgroup_dvd_card]
  rw [hker A, hker B, hc]

theorem subgroups_eq_in_cyclic
    (A B H : Subgroup G) [IsCyclic H] (hA : A ≤ H) (hB : B ≤ H)
    (hc : Nat.card A = Nat.card B) : A = B := by
  have he : A.subgroupOf H = B.subgroupOf H := by
    apply cyclic_subgroup_eq_of_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hc]
  have he' := congrArg (fun K : Subgroup H => K.map H.subtype) he
  simpa only [Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB] using he'

def commutingProduct (A B : Subgroup G)
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G)) : A × B →* G :=
  A.subtype.noncommCoprod B.subtype hcomm

theorem commutingProduct_range (A B : Subgroup G)
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G)) :
    (commutingProduct A B hcomm).range = A ⊔ B := by
  change (A.subtype.noncommCoprod B.subtype hcomm).range = A ⊔ B
  erw [MonoidHom.noncommCoprod_range]
  simp

theorem commutingProduct_injective (A B : Subgroup G)
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G))
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    Function.Injective (commutingProduct A B hcomm) :=
  Subgroup.mul_injective_of_disjoint (Subgroup.disjoint_of_coprime_natCard hcop)

theorem card_sup_of_commuting_coprime (A B : Subgroup G)
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G))
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  rw [← commutingProduct_range A B hcomm,
    ← Nat.card_congr (MonoidHom.ofInjective
      (commutingProduct_injective A B hcomm hcop)).toEquiv, Nat.card_prod]

theorem cyclic_sup_of_commuting_coprime (A B : Subgroup G)
    [IsCyclic A] [IsCyclic B]
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G))
    (hcop : (Nat.card A).Coprime (Nat.card B)) : IsCyclic (A ⊔ B : Subgroup G) := by
  let : IsCyclic (A × B) := Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, hcop⟩
  rw [← commutingProduct_range A B hcomm]
  exact isCyclic_of_surjective (commutingProduct A B hcomm).rangeRestrict
    (commutingProduct A B hcomm).rangeRestrict_surjective

end
end Conjecture55CyclicExtensions
end

/-! ### Module `NormalizerOddExtensions` -/
section
/-! Odd cyclic subgroups of a normalizer commute with its cyclic 2-subgroup. -/

namespace Conjecture55NormalizerOdd
open Conjecture55PartialCount Conjecture55CyclicExtensions
open Conjecture55Lean4Web.CyclicSum
noncomputable section
variable {G : Type*} [Group G] [Finite G]

theorem odd_normalizer_subgroup_le_centralizer
    (A : Subgroup G) [IsCyclic A] {j : ℕ} (hA : Nat.card A = 2 ^ (j + 1))
    (K : Subgroup (Subgroup.normalizer (A : Set G))) (hK : Odd (Nat.card K)) :
    K.map (Subgroup.normalizer (A : Set G)).subtype ≤ Subgroup.centralizer (A : Set G) := by
  let f := A.normalizerMonoidHom.comp K.subtype
  have hAut : Nat.card (MulAut A) = 2 ^ j := by
    rw [IsCyclic.card_mulAut, hA, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  have hcop : (Nat.card K).Coprime (Nat.card (MulAut A)) := by
    rw [hAut]
    exact hK.coprime_two_right.pow_right j
  have hf (k : K) : f k = 1 := by
    have hpow : (f k) ^ Nat.card K = 1 := by
      rw [← map_pow]
      rw [orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard k), map_one]
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hpow)
      (orderOf_dvd_natCard (f k))
  rintro x ⟨k, hk, rfl⟩
  have hmem : k ∈ A.normalizerMonoidHom.ker := hf ⟨k, hk⟩
  rwa [Subgroup.normalizerMonoidHom_ker] at hmem

def oddFactor (A : Subgroup G) {c : ℕ}
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) : Subgroup G :=
  K.1.1.map (Subgroup.normalizer (A : Set G)).subtype

theorem oddFactor_card (A : Subgroup G) {c : ℕ}
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    Nat.card (oddFactor A K) = Nat.card K.1.1 := by
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

theorem oddFactor_isCyclic (A : Subgroup G) {c : ℕ}
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) : IsCyclic (oddFactor A K) := by
  exact (Conjecture55Lean4Web.cyclicSubgroupMap
    (Subgroup.normalizer (A : Set G)).subtype K.1).2

theorem oddFactor_odd (A : Subgroup G) {c : ℕ} (hc : Odd c)
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) : Odd (Nat.card (oddFactor A K)) := by
  rw [oddFactor_card]
  exact Odd.of_dvd_nat hc K.2

theorem oddFactor_commutes (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    ∀ a : A, ∀ b : oddFactor A K, Commute (a : G) (b : G) := by
  have hle := odd_normalizer_subgroup_le_centralizer A hA K.1.1 (Odd.of_dvd_nat hc K.2)
  intro a b
  exact (Subgroup.mem_centralizer_iff.mp (hle b.2)) a.1 a.2

def extendOdd (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) : CyclicSubgroups G :=
  ⟨A ⊔ oddFactor A K, by
    let : IsCyclic (oddFactor A K) := oddFactor_isCyclic A K
    apply cyclic_sup_of_commuting_coprime _ _ (oddFactor_commutes A hA hc K)
    rw [hA]
    exact (oddFactor_odd A hc K).coprime_two_left.pow_left (j + 1)⟩

theorem extendOdd_card (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    Nat.card (extendOdd A hA hc K).1 = 2 ^ (j + 1) * Nat.card K.1.1 := by
  change Nat.card (A ⊔ oddFactor A K : Subgroup G) = _
  rw [card_sup_of_commuting_coprime _ _ (oddFactor_commutes A hA hc K) (by
    rw [hA]; exact (oddFactor_odd A hc K).coprime_two_left.pow_left (j + 1)),
    hA, oddFactor_card]

theorem extendOdd_injective (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c) :
    Function.Injective (extendOdd A hA hc) := by
  intro K L he
  have hcard := congrArg (fun H : CyclicSubgroups G => Nat.card H.1) he
  rw [extendOdd_card, extendOdd_card] at hcard
  have hKL : Nat.card K.1.1 = Nat.card L.1.1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hcard
  have hH : (extendOdd A hA hc K).1 = (extendOdd A hA hc L).1 := congrArg Subtype.val he
  let H := (extendOdd A hA hc K).1
  let : IsCyclic H := (extendOdd A hA hc K).2
  have hleL : oddFactor A L ≤ H := by rw [show H = (extendOdd A hA hc L).1 from hH]; exact le_sup_right
  have hB : oddFactor A K = oddFactor A L :=
    subgroups_eq_in_cyclic _ _ H le_sup_right hleL (by rw [oddFactor_card, oddFactor_card, hKL])
  apply Subtype.ext
  apply Subtype.ext
  exact Subgroup.map_injective (Subgroup.subtype_injective _) hB

end
end Conjecture55NormalizerOdd
end

/-! ### Module `ConjugateOddFamilies` -/
section
/-! Injective counting of conjugates of cyclic 2-subgroups, with odd factors. -/

namespace Conjecture55ConjugateOdd
open Conjecture55PartialCount Conjecture55CyclicExtensions Conjecture55NormalizerOdd
open Conjecture55Lean4Web.CyclicSum
noncomputable section
variable {G : Type*} [Group G] [Finite G]

abbrev Family (A : Subgroup G) := _root_.CyclicSum.ConjugateFamily A

def conjugator (A : Subgroup G) (T : Family A) : G := T.2.choose

theorem conjugator_spec (A : Subgroup G) (T : Family A) :
    T.1 = A.map (MulAut.conj (conjugator A T)).toMonoidHom := T.2.choose_spec

def conjugateExtension (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (x : Family A × CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    CyclicSubgroups G :=
  Conjecture55Lean4Web.cyclicSubgroupMap
    (MulAut.conj (conjugator A x.1)).toMonoidHom (extendOdd A hA hc x.2)

theorem conjugateExtension_contains (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (x : Family A × CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    x.1.1 ≤ (conjugateExtension A hA hc x).1 := by
  rw [conjugator_spec A x.1]
  exact Subgroup.map_mono le_sup_left

theorem conjugateExtension_card (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (x : Family A × CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    Nat.card (conjugateExtension A hA hc x).1 = 2 ^ (j + 1) * Nat.card x.2.1.1 := by
  change Nat.card ((extendOdd A hA hc x.2).1.map
    (MulAut.conj (conjugator A x.1)).toMonoidHom) = _
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, extendOdd_card]

theorem conjugateExtension_injective (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c) :
    Function.Injective (conjugateExtension A hA hc) := by
  rintro ⟨T, K⟩ ⟨U, L⟩ he
  let H := (conjugateExtension A hA hc (T, K)).1
  let : IsCyclic H := (conjugateExtension A hA hc (T, K)).2
  have hT : T.1 ≤ H := conjugateExtension_contains A hA hc (T, K)
  have hU : U.1 ≤ H := by
    change U.1 ≤ (conjugateExtension A hA hc (T, K)).1
    rw [he]
    exact conjugateExtension_contains A hA hc (U, L)
  have hTU : T = U := by
    apply Subtype.ext
    apply subgroups_eq_in_cyclic T.1 U.1 H hT hU
    rw [_root_.CyclicSum.conjugate_family_subgroup_card A T,
      _root_.CyclicSum.conjugate_family_subgroup_card A U]
  subst U
  have hKL : K = L := by
    apply extendOdd_injective A hA hc
    exact Conjecture55Lean4Web.cyclicSubgroupMap_injective
      (MulAut.conj (conjugator A T)).toMonoidHom (MulAut.conj _).injective he
  exact Prod.ext rfl hKL

abbrev CyclicWithTwoPart (G : Type*) [Group G] (j : ℕ) :=
  {H : CyclicSubgroups G // ∃ d : ℕ, Odd d ∧ Nat.card H.1 = 2 ^ (j + 1) * d}

def conjugateExtensionWithTwoPart (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (x : Family A × CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    CyclicWithTwoPart G j :=
  ⟨conjugateExtension A hA hc x,
    ⟨Nat.card x.2.1.1, Odd.of_dvd_nat hc x.2.2, conjugateExtension_card A hA hc x⟩⟩

theorem normalizer_index_mul_partialCount_le (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c) :
    (Subgroup.normalizer (A : Set G)).index *
      Nat.card (CyclicDividing (Subgroup.normalizer (A : Set G)) c) ≤
        Nat.card (CyclicWithTwoPart G j) := by
  have hi : Function.Injective (conjugateExtensionWithTwoPart A hA hc) := by
    intro x y he
    exact conjugateExtension_injective A hA hc (congrArg Subtype.val he)
  have h := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_prod, _root_.CyclicSum.conjugate_family_card A] at h
  exact h

/-- The normalizer's odd-divisor count can be repeated independently over
all conjugates of the cyclic 2-subgroup. -/
theorem normalizer_index_mul_divisors_le (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (hcdiv : c ∣ Nat.card (Subgroup.normalizer (A : Set G))) :
    (Subgroup.normalizer (A : Set G)).index * c.divisors.card ≤
      Nat.card (CyclicWithTwoPart G j) := by
  classical
  let := Fintype.ofFinite (Subgroup.normalizer (A : Set G))
  exact (Nat.mul_le_mul_left _ (divisors_card_le_cyclicDividing hcdiv)).trans
    (normalizer_index_mul_partialCount_le A hA hc)

end
end Conjecture55ConjugateOdd
end

/-! ### Module `SimpleNormalizerIndex` -/
section
/-! A cyclic subgroup inside a nonabelian simple subgroup has no normalizer
of odd index one or three. No classification theorem is used. -/

namespace Conjecture55SimpleNormalizer
variable {G : Type*} [Group G] [Finite G]

end Conjecture55SimpleNormalizer
end

/-! ### Module `OddSquarefreeArithmetic` -/
section
/-! The arithmetic gain from a proper odd normalizer index greater than three. -/

open scoped BigOperators
namespace Conjecture55OddSquarefree

theorem divisors_card_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne_zero]
  have he : (∏ p ∈ n.primeFactors, (n.factorization p + 1)) =
      ∏ _p ∈ n.primeFactors, 2 := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hn
      (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1]
  rw [he, Finset.prod_const]

theorem exists_prime_ge_five {n : ℕ} (hn : Squarefree n) (ho : Odd n) (h5 : 5 ≤ n) :
    ∃ p ∈ n.primeFactors, 5 ≤ p := by
  by_contra h
  push Not at h
  have hs : n.primeFactors ⊆ {3} := by
    intro p hp
    have hprime := (Nat.mem_primeFactors.mp hp).1
    have hd := (Nat.mem_primeFactors.mp hp).2.1
    have h2 : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ hd)
    have h4 : p ≠ 4 := by intro he; subst p; norm_num at hprime
    have := h p hp
    have := hprime.two_le
    simp only [Finset.mem_singleton]
    omega
  have hd : n ∣ 3 := by
    rw [← Nat.prod_primeFactors_of_squarefree hn]
    have hprod := Finset.prod_dvd_prod_of_subset n.primeFactors {3} (fun p : ℕ => p) hs
    simpa using hprod
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

/-- A nontrivial odd squarefree index other than three contributes a factor
at least 5/2 relative to its number of divisors. -/
theorem five_mul_divisors_le_two_mul {n : ℕ}
    (hn : Squarefree n) (ho : Odd n) (h5 : 5 ≤ n) :
    5 * n.divisors.card ≤ 2 * n := by
  obtain ⟨p, hp, hp5⟩ := exists_prime_ge_five hn ho h5
  have hcard := Finset.card_erase_add_one hp
  have hsmall : 2 ^ (n.primeFactors.erase p).card ≤
      ∏ q ∈ n.primeFactors.erase p, q := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ => by omega)
    intro q hq
    exact (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hq)).1.two_le
  have hprod : n = p * ∏ q ∈ n.primeFactors.erase p, q := by
    calc
      n = ∏ q ∈ n.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hn).symm
      _ = _ := (Finset.mul_prod_erase _ (fun q : ℕ => q) hp).symm
  have hb := Nat.mul_le_mul_right (∏ q ∈ n.primeFactors.erase p, q) hp5
  rw [divisors_card_of_squarefree hn, ← hcard, pow_succ]
  nlinarith

theorem normalizer_gain {m c n : ℕ}
    (hm : Squarefree m) (ho : Odd n) (h5 : 5 ≤ n) (hfactor : m = c * n) :
    5 * m.divisors.card ≤ 2 * (n * c.divisors.card) := by
  have hn : Squarefree n := Squarefree.squarefree_of_dvd
    (by rw [hfactor]; exact dvd_mul_left _ _) hm
  have hc : c.Coprime n := by
    exact Nat.coprime_of_squarefree_mul (hfactor ▸ hm)
  rw [hfactor, hc.card_divisors_mul]
  have h := five_mul_divisors_le_two_mul hn ho h5
  nlinarith

end Conjecture55OddSquarefree
end

/-! ### Module `ThreeCyclicFamilies` -/
section
/-! A classification-free counting bound from normalized cyclic subgroups
of orders two, four, and eight inside a nonabelian simple subgroup. -/

open scoped BigOperators
namespace Conjecture55ThreeFamilies
open Conjecture55PartialCount Conjecture55ConjugateOdd
open Conjecture55SimpleNormalizer Conjecture55OddSquarefree
open Conjecture55Lean4Web.CyclicSum
noncomputable section
variable {G : Type*} [Group G] [Finite G]

theorem factor_of_sylow_le {a m : ℕ} (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m) (P : Sylow 2 G)
    (N : Subgroup G) (hPN : (P : Subgroup G) ≤ N) :
    Odd N.index ∧ ∃ c, Odd c ∧ m = c * N.index ∧ Nat.card N = 2 ^ a * c := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd P.index := Nat.not_even_iff_odd.mp (by
    simpa only [even_iff_two_dvd] using P.not_dvd_index)
  have hnodd : Odd N.index := Odd.of_dvd_nat hpodd (Subgroup.index_dvd_of_le hPN)
  have hd : N.index ∣ m := by
    apply (hnodd.coprime_two_right.pow_right a).dvd_of_dvd_mul_left
    rw [← hG]
    exact N.index_dvd_card
  obtain ⟨c, hmc⟩ := hd
  have hfactor : m = c * N.index := hmc.trans (Nat.mul_comm _ _)
  have hc : Odd c := Odd.of_dvd_nat hm (by rw [hmc]; exact dvd_mul_left _ _)
  refine ⟨hnodd, c, hc, hfactor, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (m := N.index) hnodd.pos
  simpa only [hG, hfactor, mul_assoc] using N.card_mul_index

theorem two_exponents_eq {i j d e : ℕ} (hd : Odd d) (he : Odd e)
    (h : 2 ^ (i + 1) * d = 2 ^ (j + 1) * e) : i = j := by
  have factor (k t : ℕ) (ht : Odd t) :
      (2 ^ (k + 1) * t).factorization 2 = k + 1 := by
    rw [Nat.factorization_mul (by positivity) ht.pos.ne']
    simp [Nat.prime_two.factorization_pow,
      Nat.factorization_eq_zero_of_not_dvd ht.not_two_dvd_nat]
  have hf := congrArg (fun n : ℕ => n.factorization 2) h
  rw [factor _ _ hd, factor _ _ he] at hf
  omega

def forgetTwoPart : (Σ i : Fin 3, CyclicWithTwoPart G i.val) → CyclicSubgroups G :=
  fun x => x.2.1

theorem forgetTwoPart_injective : Function.Injective (forgetTwoPart (G := G)) := by
  rintro ⟨i, H⟩ ⟨j, K⟩ heq
  obtain ⟨d, hd, hHd⟩ := H.2
  obtain ⟨e, he, hKe⟩ := K.2
  have hc := congrArg (fun L : CyclicSubgroups G => Nat.card L.1) heq
  have hij : i = j := Fin.ext (two_exponents_eq hd he (hHd.symm.trans (hc.trans hKe)))
  subst j
  have hHK : H = K := Subtype.ext heq
  subst K
  rfl

theorem odd_ne_twoPart {m : ℕ} (hm : Odd m) (H : CyclicDividing G m)
    (x : Σ i : Fin 3, CyclicWithTwoPart G i.val) : H.1 ≠ forgetTwoPart x := by
  intro heq
  have ho : Odd (Nat.card H.1.1) := Odd.of_dvd_nat hm H.2
  obtain ⟨d, _, hcard⟩ := x.2.2
  have hEq := congrArg (fun L : CyclicSubgroups G => Nat.card L.1) heq
  have h2 : 2 ∣ Nat.card x.2.1.1 := by
    rw [hcard, pow_succ', mul_assoc]
    exact dvd_mul_right _ _
  exact ho.not_two_dvd_nat (hEq ▸ h2)

set_option maxHeartbeats 1000000 in
theorem cyclic_count_ge_odd_and_three_families {m : ℕ} (hm : Odd m) :
    Nat.card (CyclicDividing G m) +
      Nat.card (CyclicWithTwoPart G 0) + Nat.card (CyclicWithTwoPart G 1) +
      Nat.card (CyclicWithTwoPart G 2) ≤ Nat.card (CyclicSubgroups G) := by
  classical
  have hi : Function.Injective (Sum.elim
      (Subtype.val : CyclicDividing G m → CyclicSubgroups G) forgetTwoPart) :=
    Subtype.val_injective.sumElim forgetTwoPart_injective (odd_ne_twoPart hm)
  have h := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_sum, Nat.card_sigma] at h
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using h

end
end Conjecture55ThreeFamilies
end

/-! ### Module `FTOnly.Basic` -/
section
/-! The odd order theorem as an explicit hypothesis, and the only consequences
of it used by the FT-conditional proof: a nonabelian simple group has a
noncyclic Sylow 2-subgroup, and a radical-free group has one too. -/

namespace C55FT
open Conjecture55Lean4Web

/-- The Feit–Thompson odd order theorem, for groups in `Type`. -/
def OddOrderTheorem : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Odd (Nat.card H) → Group.IsSolvable H

theorem not_solvable_of_nontrivial_radicalFree
    {G : Type*} [Group G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    ¬ Group.IsSolvable G := by
  intro hs
  exact top_ne_bot (hrad ⊤ inferInstance inferInstance)

/-- The automorphism group of a cyclic 2-group is a 2-group. -/
theorem isPGroup_mulAut_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q]
    (hQ : IsPGroup 2 Q) : IsPGroup 2 (MulAut Q) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · apply IsPGroup.of_card (n := 0)
    rw [IsCyclic.card_mulAut, hn]
    simp
  · apply IsPGroup.of_card (n := n - 1)
    rw [IsCyclic.card_mulAut, hn, Nat.totient_prime_pow Nat.prime_two hpos]
    simp

/-- A noncyclic 2-group has order divisible by four. -/
theorem four_dvd_card_of_not_isCyclic {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hnc : ¬ IsCyclic Q) : 4 ∣ Nat.card Q := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have h2 : 2 ≤ n := by
    by_contra h
    apply hnc
    apply isCyclic_of_card_dvd_prime (p := 2)
    rw [hn]
    interval_cases n <;> norm_num
  rw [hn]
  exact (by norm_num : (4 : ℕ) = 2 ^ 2) ▸ pow_dvd_pow 2 h2

variable (hFT : OddOrderTheorem)
include hFT

/-- A cyclic Sylow 2-subgroup forces solvability, given the odd order theorem. -/
theorem isSolvable_of_isCyclic_sylow_two (G : Type) [Group G] [Finite G]
    (P : Sylow 2 G) (hP : IsCyclic P) : Group.IsSolvable G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsMulCommutative P := IsMulCommutative.of_comm (fun x y => by
    obtain ⟨g, hg⟩ := hP.exists_generator
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    rw [← zpow_add, ← zpow_add, add_comm])
  have hAut : IsPGroup 2 (MulAut P) := isPGroup_mulAut_of_isCyclic P.isPGroup'
  obtain ⟨N, hN, hcomp⟩ := SylowInputs.exists_normal_complement_of_aut_isPGroup P hAut
  let : N.Normal := hN
  have hcard : Nat.card N = P.index := hcomp.index_eq_card.symm
  have hodd : Odd (Nat.card N) := by
    rw [hcard]
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using P.not_dvd_index)
  let : Group.IsSolvable N := hFT N hodd
  let : Group.IsSolvable P := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  have hQ : Group.IsSolvable (G ⧸ N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := hcomp.symm.QuotientMulEquiv.toMonoidHom) hcomp.symm.QuotientMulEquiv.injective
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, hQ⟩

/-- A nontrivial radical-free group has a noncyclic Sylow 2-subgroup. -/
theorem not_isCyclic_sylow_two_of_radicalFree (G : Type) [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (P : Sylow 2 G) : ¬ IsCyclic P := fun hP =>
  not_solvable_of_nontrivial_radicalFree hrad (isSolvable_of_isCyclic_sylow_two hFT G P hP)

theorem not_isCyclic_sylow_two_of_simple (H : Type) [Group H] [Finite H]
    (hs : IsSimpleGroup H) (hn : ¬ IsMulCommutative H) (Q : Sylow 2 H) : ¬ IsCyclic Q := by
  intro hQ
  have hsol := isSolvable_of_isCyclic_sylow_two hFT H Q hQ
  exact hn (IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr hsol))

theorem four_dvd_card_of_simple (H : Type) [Group H] [Finite H]
    (hs : IsSimpleGroup H) (hn : ¬ IsMulCommutative H) : 4 ∣ Nat.card H := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 H := default
  exact (four_dvd_card_of_not_isCyclic Q.isPGroup'
    (not_isCyclic_sylow_two_of_simple hFT H hs hn Q)).trans
    (Subgroup.card_subgroup_dvd_card (Q : Subgroup H))

theorem exists_involution_of_simple (H : Type) [Group H] [Finite H]
    (hs : IsSimpleGroup H) (hn : ¬ IsMulCommutative H) : ∃ x : H, orderOf x = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' 2
    ((by norm_num : (2 : ℕ) ∣ 4).trans (four_dvd_card_of_simple hFT H hs hn))

end C55FT
end

/-! ### Module `FTOnly.Normalizer` -/
section
/-! Normalizers in a group whose nonabelian simple normal subgroup has trivial
centralizer.  No classification theorem is used. -/

namespace C55FT
open Conjecture55Lean4Web

variable {G : Type*} [Group G] [Finite G]

/-- A nonabelian simple subgroup that normalizes a cyclic subgroup centralizes it,
because the automorphism group of a cyclic group is commutative. -/
theorem le_centralizer_of_le_normalizer (S A : Subgroup G) (hs : IsSimpleGroup S)
    (hn : ¬ IsMulCommutative S) [IsCyclic A]
    (hSN : S ≤ Subgroup.normalizer (A : Set G)) :
    S ≤ Subgroup.centralizer (A : Set G) := by
  let f : S →* (ZMod (Nat.card A))ˣ :=
    (IsCyclic.mulAutMulEquiv A).toMonoidHom.comp
      (A.normalizerMonoidHom.comp (Subgroup.inclusion hSN))
  rcases hs.eq_bot_or_eq_top_of_normal f.ker with hbot | htop
  · exfalso
    apply hn
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hbot
    exact IsMulCommutative.of_comm fun x y => hinj (by rw [map_mul, map_mul, mul_comm])
  · intro s hs'
    have hk : (⟨s, hs'⟩ : S) ∈ f.ker := htop ▸ Subgroup.mem_top _
    have h1 : A.normalizerMonoidHom (Subgroup.inclusion hSN ⟨s, hs'⟩) = 1 := by
      apply (IsCyclic.mulAutMulEquiv A).injective
      simpa [f] using hk
    have hmem : Subgroup.inclusion hSN ⟨s, hs'⟩ ∈ A.normalizerMonoidHom.ker := h1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmem
    exact hmem

/-- Consequently a nontrivial cyclic subgroup is not normalized by such an `S`. -/
theorem not_le_normalizer_of_cyclic (S A : Subgroup G) (hs : IsSimpleGroup S)
    (hn : ¬ IsMulCommutative S) (hC : Subgroup.centralizer (S : Set G) = ⊥)
    [IsCyclic A] (hA : A ≠ ⊥) : ¬ S ≤ Subgroup.normalizer (A : Set G) := by
  intro hSN
  have h := le_centralizer_of_le_normalizer S A hs hn hSN
  rw [Subgroup.le_centralizer_iff, hC] at h
  exact hA (le_bot_iff.mp h)

/-- If a simple normal subgroup with trivial centralizer is not contained in `H`,
then the action on the cosets of `H` is faithful. -/
theorem normalCore_eq_bot_of_not_le (S : Subgroup G) [S.Normal] (hs : IsSimpleGroup S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) (H : Subgroup G) (hSH : ¬ S ≤ H) :
    H.normalCore = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (H.normalCore.subgroupOf S) with hb | ht
  · have hdisj : Disjoint H.normalCore S := by
      rw [Subgroup.disjoint_def]
      intro x hx hxS
      have hmem : (⟨x, hxS⟩ : S) ∈ H.normalCore.subgroupOf S := hx
      rw [hb] at hmem
      simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    apply le_bot_iff.mp
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hsS
      exact (Subgroup.commute_of_normal_of_disjoint H.normalCore S inferInstance
        inferInstance hdisj x s hx hsS).symm
    rwa [hC] at hxC
  · exact (hSH ((Subgroup.subgroupOf_eq_top.mp ht).trans H.normalCore_le)).elim

/-- A faithful action on the cosets of `H` embeds the group in a symmetric group. -/
theorem card_dvd_factorial_index (H : Subgroup G) (h : H.normalCore = ⊥) :
    Nat.card G ∣ H.index.factorial := by
  have hd : H.normalCore.index ∣ H.index.factorial := by
    rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker, Subgroup.index_eq_card,
      ← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ H)).range
  rwa [h, Subgroup.index_bot] at hd

/-- The normalizer of a nontrivial cyclic subgroup has odd index at least five.
Unlike the chain argument, the subgroup need not lie in `S`. -/
theorem normalizer_index_ge_five (S : Subgroup G) [S.Normal] (hs : IsSimpleGroup S)
    (hn : ¬ IsMulCommutative S) (h4 : 4 ∣ Nat.card S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥)
    (A : Subgroup G) [IsCyclic A] (hA : A ≠ ⊥)
    (ho : Odd (Subgroup.normalizer (A : Set G)).index) :
    5 ≤ (Subgroup.normalizer (A : Set G)).index := by
  have hnot := not_le_normalizer_of_cyclic S A hs hn hC hA
  have h1 : (Subgroup.normalizer (A : Set G)).index ≠ 1 := by
    intro he
    exact hnot ((Subgroup.index_eq_one.mp he) ▸ le_top)
  have h3 : (Subgroup.normalizer (A : Set G)).index ≠ 3 := by
    intro he
    have hd := card_dvd_factorial_index _ (normalCore_eq_bot_of_not_le S hs hC _ hnot)
    rw [he] at hd
    have h46 : 4 ∣ 6 := h4.trans ((Subgroup.card_subgroup_dvd_card S).trans hd)
    norm_num at h46
  have hpos := ho.pos
  have hmod := Nat.odd_iff.mp ho
  omega

end C55FT
end

/-! ### Module `FTOnly.Arith` -/
section
/-! Elementary bounds on `2 ^ ω(n)` used by the FT-conditional counting. -/

namespace C55FT
open Conjecture55Lean4Web

/-- For odd `n`, one has `3 * 4 ^ ω(n) ≤ 4 * n`: every odd prime other than
three is at least four. -/
theorem three_mul_four_pow_card_primeFactors_le {n : ℕ} (hn : Odd n) :
    3 * 4 ^ n.primeFactors.card ≤ 4 * n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hprod : ∏ p ∈ n.primeFactors, p ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.prod_primeFactors_dvd n)
  have hodd (p : ℕ) (hp : p ∈ n.primeFactors) : 3 ≤ p := by
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hpd := (Nat.mem_primeFactors.mp hp).2.1
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hpd)
    have := hpp.two_le
    omega
  by_cases h3 : 3 ∈ n.primeFactors
  · have hcard := Finset.card_erase_add_one h3
    have hrest : 4 ^ (n.primeFactors.erase 3).card ≤ ∏ p ∈ n.primeFactors.erase 3, p := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod₀ (fun _ _ => by omega)
      intro p hp
      have hne := Finset.ne_of_mem_erase hp
      have := hodd p (Finset.mem_of_mem_erase hp)
      have hpp := (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hpp
      omega
    have hsplit : ∏ p ∈ n.primeFactors, p = 3 * ∏ p ∈ n.primeFactors.erase 3, p :=
      (Finset.mul_prod_erase _ (fun p : ℕ => p) h3).symm
    rw [← hcard, pow_succ]
    nlinarith
  · have hall : 4 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod₀ (fun _ _ => by omega)
      intro p hp
      have hne : p ≠ 3 := fun h => h3 (h ▸ hp)
      have := hodd p hp
      have hpp := (Nat.mem_primeFactors.mp hp).1
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hpp
      omega
    omega

theorem card_primeFactors_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
  rw [Nat.primeFactors_mul ha hb]
  exact Finset.card_union_le _ _

/-- The divisor count of a cofactor dominates the loss in `2 ^ ω`. -/
theorem two_pow_card_primeFactors_le_mul {m c n : ℕ} (hm : m = c * n) (hm0 : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ 2 ^ n.primeFactors.card * c.divisors.card := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hm; exact hm0 hm
  have hn0 : n ≠ 0 := by rintro rfl; simp at hm; exact hm0 hm
  have hle := card_primeFactors_mul_le hc0 hn0
  rw [← hm] at hle
  calc 2 ^ m.primeFactors.card ≤ 2 ^ (c.primeFactors.card + n.primeFactors.card) :=
        Nat.pow_le_pow_right (by norm_num) hle
    _ = 2 ^ n.primeFactors.card * 2 ^ c.primeFactors.card := by rw [pow_add, mul_comm]
    _ ≤ 2 ^ n.primeFactors.card * c.divisors.card :=
        Nat.mul_le_mul_left _ (two_pow_card_primeFactors_le_card_divisors c (Nat.pos_of_ne_zero hc0))

/-- For odd `n ≥ 7`, the ratio `n / 2 ^ ω(n)` is at least `7 / 2`. -/
theorem seven_mul_two_pow_le_two_mul {n : ℕ} (hn : Odd n) (h7 : 7 ≤ n) :
    7 * 2 ^ n.primeFactors.card ≤ 2 * n := by
  by_cases hsmall : n ≤ 16
  · obtain ⟨k, rfl⟩ := hn
    have hk : k ≤ 8 := by omega
    interval_cases k <;> first | omega | (norm_num [Nat.primeFactors, Nat.primeFactorsList_ofNat])
  · have h1 := three_mul_four_pow_card_primeFactors_le hn
    have h4 : 4 ^ n.primeFactors.card = (2 ^ n.primeFactors.card) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4] at h1
    nlinarith

/-- The odd integers `n ≥ 5` with `n / 2 ^ ω(n) < 7`. -/
theorem mem_small_of_lt_seven_mul {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n)
    (hlt : n < 7 * 2 ^ n.primeFactors.card) :
    n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 11 ∨ n = 13 ∨ n = 15 ∨ n = 21 := by
  have hbound : n ≤ 65 := by
    have h1 := three_mul_four_pow_card_primeFactors_le hn
    have h4 : 4 ^ n.primeFactors.card = (2 ^ n.primeFactors.card) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4] at h1
    nlinarith
  obtain ⟨k, rfl⟩ := hn
  have hk : k ≤ 32 := by omega
  interval_cases k <;> first | omega | (norm_num [Nat.primeFactors, Nat.primeFactorsList_ofNat] at hlt)

end C55FT
end

/-! ### Module `FTOnly.Families` -/
section
/-! Shared counting tools for the FT-conditional proof: the family attached to a
normalized cyclic 2-subgroup, normalizers of powers of an index-two cyclic
subgroup, and Sylow counts when the odd part of the order is fifteen. -/

namespace C55FT
open Conjecture55Lean4Web Conjecture55PartialCount Conjecture55ConjugateOdd
open Conjecture55ThreeFamilies

section Families
variable {G : Type*} [Group G] [Finite G]

/-- The normalizer of a cyclic 2-subgroup containing a Sylow subgroup has odd index
`n`, and `n * τ(m / n)` cyclic subgroups have the same 2-part as the subgroup. -/
theorem family_bound {a m j : ℕ} (hm : Odd m) (hG : Nat.card G = 2 ^ a * m)
    (P : Sylow 2 G) (A : Subgroup G) [IsCyclic A] (hA : Nat.card A = 2 ^ (j + 1))
    (hPN : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G)) :
    ∃ c, Odd c ∧ m = c * (Subgroup.normalizer (A : Set G)).index ∧
      Odd (Subgroup.normalizer (A : Set G)).index ∧
      (Subgroup.normalizer (A : Set G)).index * c.divisors.card ≤
        Nat.card (CyclicWithTwoPart G j) := by
  obtain ⟨ho, c, hc, hmc, hNC⟩ := factor_of_sylow_le hm hG P _ hPN
  exact ⟨c, hc, hmc, ho,
    normalizer_index_mul_divisors_le A hA hc (by rw [hNC]; exact dvd_mul_left _ _)⟩

/-- Every power of a generator of an index-two cyclic subgroup of `P` generates
a subgroup normalized by `P`. -/
theorem le_normalizer_zpowers_pow (P : Subgroup G) (g : P)
    (hidx : (Subgroup.zpowers g).index = 2) (e : ℕ) :
    P ≤ Subgroup.normalizer ((Subgroup.zpowers ((g : G) ^ e) : Subgroup G) : Set G) := by
  have hnorm : (Subgroup.zpowers g).Normal := Subgroup.normal_of_index_eq_two hidx
  have hfwd : ∀ p ∈ P, ∀ b ∈ Subgroup.zpowers ((g : G) ^ e),
      p * b * p⁻¹ ∈ Subgroup.zpowers ((g : G) ^ e) := by
    intro p hp b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hconj : (⟨p, hp⟩ : P) * g * (⟨p, hp⟩ : P)⁻¹ ∈ Subgroup.zpowers g :=
      hnorm.conj_mem g (Subgroup.mem_zpowers g) ⟨p, hp⟩
    obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.mp hconj
    have hu' : p * (g : G) * p⁻¹ = (g : G) ^ u := by
      have := congrArg Subtype.val hu
      simpa using this.symm
    refine Subgroup.mem_zpowers_iff.mpr ⟨u * k, ?_⟩
    have key : p * ((g : G) ^ e) ^ k * p⁻¹ = ((g : G) ^ e) ^ (u * k) := by
      rw [← zpow_natCast, ← zpow_mul, ← conj_zpow, hu', ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    exact key.symm
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hfwd p hp h
  · intro hh
    have := hfwd p⁻¹ (P.inv_mem hp) _ hh
    simpa [mul_assoc] using this

end Families

section Sylow
variable {G : Type*} [Group G] [Finite G]

theorem card_sylow_eq_prime {p : ℕ} [Fact p.Prime] (Q : Sylow p G)
    (hp : p ∣ Nat.card G) (hp2 : ¬ p ^ 2 ∣ Nat.card G) : Nat.card Q = p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have h1 : p ∣ Nat.card Q := by
    simpa using Q.pow_dvd_card_of_pow_dvd_card (n := 1) (by simpa using hp)
  have h2 : Nat.card Q ∣ Nat.card G := Subgroup.card_subgroup_dvd_card (Q : Subgroup G)
  have hp1 := (Fact.out : p.Prime).one_lt
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · rw [hk, pow_zero] at h1
      exact absurd (Nat.le_of_dvd one_pos h1) (by omega)
    · rw [hk, pow_one]
  · exact absurd ((pow_dvd_pow p hk2).trans (hk ▸ h2)) hp2

/-- A normal Sylow subgroup of prime order contradicts radical-freeness. -/
theorem sylow_not_subsingleton {p : ℕ} [Fact p.Prime]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (Q : Sylow p G) (hQ : Nat.card Q = p) : ¬ Subsingleton (Sylow p G) := by
  intro hsub
  have hQn : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  let : IsCyclic Q := isCyclic_of_prime_card hQ
  let : Group.IsSolvable Q := Group.isSolvable_of_comm (fun x y => by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    rw [← zpow_add, ← zpow_add, add_comm])
  have hbot := hrad Q hQn inferInstance
  have h1 : Nat.card Q = 1 := by rw [hbot, Subgroup.card_bot]
  have := (Fact.out : p.Prime).one_lt
  omega

theorem card_sylow_ge_two {p : ℕ} [Fact p.Prime]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (Q : Sylow p G) (hQ : Nat.card Q = p) : 2 ≤ Nat.card (Sylow p G) := by
  have hpos : 0 < Nat.card (Sylow p G) := Nat.card_pos
  by_contra h
  have h1 : Nat.card (Sylow p G) = 1 := by omega
  exact sylow_not_subsingleton hrad Q hQ (Finite.card_le_one_iff_subsingleton.mp h1.le)

/-- The group order `40` is impossible for a radical-free group. -/
theorem false_of_card_forty
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hcard : Nat.card G = 40) : False := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let Q : Sylow 5 G := default
  have hQ : Nat.card Q = 5 := card_sylow_eq_prime Q (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num)
  have hmod := card_sylow_modEq_one 5 G
  have hdvd : Nat.card (Sylow 5 G) ∣ 8 := by
    have h := Q.card_dvd_index
    have hi : (Q : Subgroup G).index = 8 := by
      have := (Q : Subgroup G).card_mul_index
      rw [hQ, hcard] at this
      omega
    rwa [hi] at h
  have h2 := card_sylow_ge_two hrad Q hQ
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases h : Nat.card (Sylow 5 G) <;> omega

/-- When `|G| = 60` or `120`, there are at least seventeen cyclic subgroups of
order dividing fifteen: the identity, ten of order three, and six of order five. -/
theorem seventeen_le_cyclicDividing_fifteen [Fintype G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (S : Subgroup G) [S.Normal] (hs : IsSimpleGroup S) (hn : ¬ IsMulCommutative S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥)
    (hcard : Nat.card G = 60 ∨ Nat.card G = 120) :
    17 ≤ Nat.card (CyclicDividing G 15) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hc5 (Q : Sylow 5 G) : Nat.card Q = 5 :=
    card_sylow_eq_prime Q (by rcases hcard with h | h <;> rw [h] <;> norm_num)
      (by rcases hcard with h | h <;> rw [h] <;> norm_num)
  have hc3 (Q : Sylow 3 G) : Nat.card Q = 3 :=
    card_sylow_eq_prime Q (by rcases hcard with h | h <;> rw [h] <;> norm_num)
      (by rcases hcard with h | h <;> rw [h] <;> norm_num)
  -- Six Sylow 5-subgroups.
  have hn5 : 6 ≤ Nat.card (Sylow 5 G) := by
    let Q : Sylow 5 G := default
    have hmod := card_sylow_modEq_one 5 G
    have hdvd : Nat.card (Sylow 5 G) ∣ 24 := by
      have hi : (Q : Subgroup G).index ∣ 24 := by
        have := (Q : Subgroup G).card_mul_index
        rw [hc5 Q] at this
        have hv : (Q : Subgroup G).index = 12 ∨ (Q : Subgroup G).index = 24 := by
          rcases hcard with h | h <;> rw [h] at this <;> omega
        rcases hv with hv | hv <;> rw [hv] <;> norm_num
      exact Q.card_dvd_index.trans hi
    have h2 := card_sylow_ge_two hrad Q (hc5 Q)
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 G) <;> omega
  -- Ten Sylow 3-subgroups: four would embed the group in the symmetric group S4.
  have hn3 : 10 ≤ Nat.card (Sylow 3 G) := by
    let Q : Sylow 3 G := default
    have hmod := card_sylow_modEq_one 3 G
    have hdvd : Nat.card (Sylow 3 G) ∣ 40 := by
      have hi : (Q : Subgroup G).index ∣ 40 := by
        have := (Q : Subgroup G).card_mul_index
        rw [hc3 Q] at this
        have hv : (Q : Subgroup G).index = 20 ∨ (Q : Subgroup G).index = 40 := by
          rcases hcard with h | h <;> rw [h] at this <;> omega
        rcases hv with hv | hv <;> rw [hv] <;> norm_num
      exact Q.card_dvd_index.trans hi
    have h2 := card_sylow_ge_two hrad Q (hc3 Q)
    have hne4 : Nat.card (Sylow 3 G) ≠ 4 := by
      intro h4
      let : IsCyclic Q := isCyclic_of_prime_card (hc3 Q)
      have hQbot : (Q : Subgroup G) ≠ ⊥ := by
        intro hb
        have := hc3 Q
        rw [hb, Subgroup.card_bot] at this
        omega
      have hnot := not_le_normalizer_of_cyclic S Q hs hn hC hQbot
      have hcore := normalCore_eq_bot_of_not_le S hs hC _ hnot
      have hd := card_dvd_factorial_index _ hcore
      have hidx : (Subgroup.normalizer ((Q : Subgroup G) : Set G)).index = 4 := by
        rw [← h4]
        exact (Sylow.card_eq_index_normalizer Q).symm
      rw [hidx] at hd
      rcases hcard with h | h <;> rw [h] at hd <;> norm_num [Nat.factorial] at hd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 3 G) <;> omega
  -- Inject the identity and the Sylow 3- and 5-subgroups.
  let e1 : Unit → CyclicDividing G 15 := fun _ => ⟨⟨⊥, inferInstance⟩, by simp⟩
  let e3 : Sylow 3 G → CyclicDividing G 15 := fun Q =>
    ⟨⟨Q, isCyclic_of_prime_card (hc3 Q)⟩, by
      change Nat.card (Q : Subgroup G) ∣ 15
      rw [hc3 Q]; norm_num⟩
  let e5 : Sylow 5 G → CyclicDividing G 15 := fun Q =>
    ⟨⟨Q, isCyclic_of_prime_card (hc5 Q)⟩, by
      change Nat.card (Q : Subgroup G) ∣ 15
      rw [hc5 Q]; norm_num⟩
  have hcard1 (u : Unit) : Nat.card (e1 u).1.1 = 1 := by simp [e1]
  have hcard3 (Q : Sylow 3 G) : Nat.card (e3 Q).1.1 = 3 := hc3 Q
  have hcard5 (Q : Sylow 5 G) : Nat.card (e5 Q).1.1 = 5 := hc5 Q
  have hi3 : Function.Injective e3 := by
    intro Q Q' h
    exact Sylow.ext (congrArg (fun K : CyclicDividing G 15 => K.1.1) h)
  have hi5 : Function.Injective e5 := by
    intro Q Q' h
    exact Sylow.ext (congrArg (fun K : CyclicDividing G 15 => K.1.1) h)
  have hi35 : Function.Injective (Sum.elim e3 e5) := by
    refine hi3.sumElim hi5 ?_
    intro Q Q' h
    have hc := congrArg (fun K : CyclicDividing G 15 => Nat.card K.1.1) h
    simp only [hcard3, hcard5] at hc
    omega
  have hi : Function.Injective (Sum.elim e1 (Sum.elim e3 e5)) := by
    refine (Function.injective_of_subsingleton e1).sumElim hi35 ?_
    intro u x h
    have hc := congrArg (fun K : CyclicDividing G 15 => Nat.card K.1.1) h
    rcases x with Q | Q
    · simp only [Sum.elim_inl, hcard1, hcard3] at hc; omega
    · simp only [Sum.elim_inr, hcard1, hcard5] at hc; omega
  have hle := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_sum, Nat.card_sum, Nat.card_unique] at hle
  omega

end Sylow

end C55FT
end

/-! ### Module `ElementaryRoots` -/
section
/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

/-!
# Root counts when no element order is divisible by four

Ordinary root lower bounds suffice for the bound by eight times the number
of divisors of the odd part; no enhanced root bound is assumed.
-/

namespace RootWeights
noncomputable section

end
end RootWeights
end

/-! ### Module `RootShape` -/
section
/-! Actual divisor-count bounds imply the small order shape and the FC threshold. -/

namespace Conjecture55RootShape
open Conjecture55Lean4Web

/-- The divisor-count bound `8 τ(m)` already reaches the exact FC threshold.
The conclusion holds for every positive two-part exponent, in particular `a ≥ 3`. -/
theorem threshold_le_of_eight_mul_divisor_count
    {G : Type*} [Group G] [Fintype G]
    (a m : ℕ) (ha : 1 ≤ a) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ a * m)
    (hcount : 8 * m.divisors.card ≤ cyc G) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  have h2 : ¬ 2 ∣ m := by
    simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm
  have hω : numPrimeFactors G = m.primeFactors.card + 1 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
    rw [hcard]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 a m Nat.prime_two ha hm.pos h2
  have hexp : 2 ^ (numPrimeFactors G + 2) = 8 * 2 ^ m.primeFactors.card := by
    rw [hω, show m.primeFactors.card + 1 + 2 = m.primeFactors.card + 3 by omega,
      pow_add]
    ring
  rw [hexp]
  exact (Nat.mul_le_mul_left 8 (two_pow_card_primeFactors_le_card_divisors m hm.pos)).trans
    hcount

end Conjecture55RootShape
end

/-! ### Module `ExponentBounds` -/
section
/-! Sylow exponent bounds give a direct, quantitative cyclic-subgroup lower
bound. Ordinary root lower bounds remain explicit; no comparison bijection or
exact-root subgroup theorem is used. -/

open scoped BigOperators

namespace RootWeights
universe u
noncomputable section

/-- A bound for the exponent of one Sylow subgroup holds for every p-element. -/
theorem pow_eq_one_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s a : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (x : G) (hx : x ^ (p ^ a) = 1) : x ^ (p ^ s) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp
    (orderOf_dvd_of_pow_eq_one hx)
  have hX : IsPGroup p (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hk]
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  let y : Q := ⟨x, hQ (Subgroup.mem_zpowers x)⟩
  let e : Q ≃* P := Q.equiv P
  have hy : y ^ (p ^ s) = 1 := by
    apply e.injective
    simpa using hP (e y)
  exact congrArg (fun z : Q => (z : G)) hy

/-- Above the Sylow exponent, the p-part of a root exponent can be lowered.
No root-count divisibility theorem is used. -/
theorem roots_eq_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s j a d : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (hsj : s ≤ j) (hja : j ≤ a) :
    {x : G | x ^ (p ^ j * d) = 1} = {x : G | x ^ (p ^ a * d) = 1} := by
  ext x
  constructor
  · intro hx
    exact orderOf_dvd_of_pow_eq_one hx |>.trans
      (Nat.mul_dvd_mul_right (pow_dvd_pow p hja) d) |>
      orderOf_dvd_iff_pow_eq_one.mp
  · intro hx
    have hxd : (x ^ d) ^ (p ^ a) = 1 := by
      simpa [pow_mul, mul_comm] using hx
    have hs := pow_eq_one_of_sylow_exponent_bound hp P hP (x ^ d) hxd
    have hj : (x ^ d) ^ (p ^ j) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_pow_eq_one hs).trans (pow_dvd_pow p hsj))
    simpa [pow_mul, mul_comm] using hj

theorem card_roots_eq_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s j a d : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (hsj : s ≤ j) (hja : j ≤ a) :
    Nat.card {x : G // x ^ (p ^ j * d) = 1} =
      Nat.card {x : G // x ^ (p ^ a * d) = 1} := by
  have he := roots_eq_of_sylow_exponent_bound (d := d) hp P hP hsj hja
  exact Nat.card_congr (Set.equivOfEq he)

theorem root_lower_bound_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s j a m d : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (hcard : Nat.card G = p ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hd : d ∣ m) (hsj : s ≤ j) (hja : j ≤ a) :
    p ^ a * d ≤ Nat.card {x : G // x ^ (p ^ j * d) = 1} := by
  rw [card_roots_eq_of_sylow_exponent_bound hp P hP hsj hja]
  apply hbase
  rw [hcard]
  exact Nat.mul_dvd_mul_left _ hd

theorem orderOf_dvd_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s a m : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (hcard : Nat.card G = p ^ a * m) (hsa : s ≤ a) (x : G) :
    orderOf x ∣ p ^ s * m := by
  have hx : x ^ (p ^ a * m) = 1 := by
    rw [← hcard]
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard x)
  have he := roots_eq_of_sylow_exponent_bound (d := m) hp P hP le_rfl hsa
  have hx' : x ∈ {x : G | x ^ (p ^ a * m) = 1} := hx
  rw [← he] at hx'
  exact orderOf_dvd_of_pow_eq_one hx'

/-- Nonnegative weighted root averages also compare formal linear combinations
of cyclic counts. The finite groups themselves need not be in bijection. -/
theorem cyclic_count_linear_comparison
    {G H K : Type*} [Group G] [Group H] [Group K]
    [Fintype G] [Fintype H] [Fintype K] {n : ℕ} [NeZero n] (c : ℕ)
    (hG : ∀ x : G, orderOf x ∣ n) (hH : ∀ x : H, orderOf x ∣ n)
    (hK : ∀ x : K, orderOf x ∣ n)
    (hroot : ∀ d ∈ n.divisors,
      (c + 1) * Nat.card {x : H // x ^ d = 1} ≤
        Nat.card {x : G // x ^ d = 1} + c * Nat.card {x : K // x ^ d = 1}) :
    (c + 1) * Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups H) ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) +
        c * Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups K) := by
  have hsum : (∑ u : (ZMod n)ˣ, ((c : ℚ) + 1) *
        (Nat.card {x : H // x ^ rootDivisor n u = 1} : ℚ)) ≤
      ∑ u : (ZMod n)ˣ, ((Nat.card {x : G // x ^ rootDivisor n u = 1} : ℚ) +
        c * (Nat.card {x : K // x ^ rootDivisor n u = 1} : ℚ)) := by
    apply Finset.sum_le_sum
    intro u _
    exact_mod_cast hroot _
      (Nat.mem_divisors.mpr ⟨rootDivisor_dvd n u, NeZero.ne n⟩)
  have hq := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n.totient : (0 : ℚ) ≤ _)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc,
    ← cyclic_count_eq_unit_average hG, ← cyclic_count_eq_unit_average hH,
    ← cyclic_count_eq_unit_average hK] at hq
  exact_mod_cast hq

theorem divisor_not_dvd_half_eq
    {s m e : ℕ} (hs : 1 ≤ s) (hm : Odd m)
    (he : e ∣ 2 ^ s * m) (hne : ¬ e ∣ 2 ^ (s - 1) * m) :
    ∃ d, d ∣ m ∧ e = 2 ^ s * d := by
  have hmpos := hm.pos
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he (by positivity)
  obtain ⟨j, d, hdOdd, heq⟩ := Nat.exists_eq_two_pow_mul_odd hepos.ne'
  have hj : j ≤ s := by
    apply (Nat.pow_dvd_pow_iff_le_right Nat.prime_two.one_lt).mp
    apply (hm.coprime_two_left.pow_left j).dvd_of_dvd_mul_right
    apply dvd_trans _ he
    rw [heq]
    exact dvd_mul_right _ _
  have hd : d ∣ m := by
    apply (hdOdd.coprime_two_right.pow_right s).dvd_of_dvd_mul_left
    apply dvd_trans _ he
    rw [heq]
    exact dvd_mul_left _ _
  have hjs : j = s := by
    by_contra h
    apply hne
    rw [heq]
    exact mul_dvd_mul (pow_dvd_pow 2 (by omega)) hd
  exact ⟨d, hd, by simpa [hjs] using heq⟩

theorem gcd_half_two_pow_mul
    {s m d : ℕ} (hs : 1 ≤ s) (hm : Odd m) (hd : d ∣ m) :
    Nat.gcd (2 ^ (s - 1) * m) (2 ^ s * d) = 2 ^ (s - 1) * d := by
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  rw [hpow, mul_assoc, Nat.gcd_mul_left]
  congr 1
  rw [Nat.gcd_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd hm.coprime_two_left hd

/-- Root estimates at the largest 2-power divisor yield a cyclic-count bound.
This uses a linear combination of two cyclic groups and positivity of the
unit-average weights, rather than a comparison bijection. -/
theorem cyclic_count_ge_of_top_root_bounds
    {G : Type*} [Group G] [Fintype G] {s m c : ℕ} (hs : 1 ≤ s) (hm : Odd m)
    (horder : ∀ x : G, orderOf x ∣ 2 ^ s * m)
    (hbase : ∀ e, e ∣ 2 ^ s * m → e ≤ Nat.card {x : G // x ^ e = 1})
    (htop : ∀ d, d ∣ m → (c + 2) * (2 ^ (s - 1) * d) ≤
      Nat.card {x : G // x ^ (2 ^ s * d) = 1}) :
    (s + c + 1) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hmpos := hm.pos
  let : NeZero (2 ^ s * m) := ⟨by positivity⟩
  let : NeZero (2 ^ (s - 1) * m) := ⟨by positivity⟩
  let H := Multiplicative (ZMod (2 ^ s * m))
  let K := Multiplicative (ZMod (2 ^ (s - 1) * m))
  have hH : Nat.card H = 2 ^ s * m := by simp [H]
  have hK : Nat.card K = 2 ^ (s - 1) * m := by simp [K]
  have hhalf : 2 ^ (s - 1) * m ∣ 2 ^ s * m :=
    Nat.mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) m
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  have hlinear := cyclic_count_linear_comparison (G := G) (H := H) (K := K)
    (n := 2 ^ s * m) c horder
    (fun x => by simpa only [hH] using orderOf_dvd_natCard x)
    (fun x => (show orderOf x ∣ 2 ^ (s - 1) * m from by
      simpa only [hK] using orderOf_dvd_natCard x).trans hhalf) (by
      intro e he
      have hed := (Nat.mem_divisors.mp he).1
      rw [card_roots_cyclic, card_roots_cyclic, hH, hK, Nat.gcd_eq_right hed]
      by_cases hehalf : e ∣ 2 ^ (s - 1) * m
      · rw [Nat.gcd_eq_right hehalf]
        have hb := hbase e hed
        nlinarith
      · obtain ⟨d, hd, rfl⟩ := divisor_not_dvd_half_eq hs hm hed hehalf
        rw [gcd_half_two_pow_mul hs hm hd]
        have ht := htop d hd
        rw [hpow] at ht ⊢
        nlinarith)
  have hcH : Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups H) =
      (s + 1) * m.divisors.card := by
    rw [Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_divisors_card, hH,
      (hm.coprime_two_left.pow_left s).card_divisors_mul,
      Nat.divisors_prime_pow Nat.prime_two]
    simp
  have hcK : Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups K) =
      s * m.divisors.card := by
    rw [Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_divisors_card, hK,
      (hm.coprime_two_left.pow_left (s - 1)).card_divisors_mul,
      Nat.divisors_prime_pow Nat.prime_two]
    simp [Nat.sub_add_cancel hs]
  rw [hcH, hcK] at hlinear
  nlinarith

/-- Proposition E: ordinary root lower bounds and a bound on the Sylow
2-exponent imply the precise lower bound `(s-1+2^(a-s+1)) τ(m)`.
The ordinary root lower bound is explicitly assumed. -/
theorem cyclic_count_ge_of_sylow_exponent_bound
    {G : Type*} [Group G] [Fintype G] {s a m : ℕ}
    (hs : 1 ≤ s) (hsa : s ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hP : ∀ x : P, x ^ (2 ^ s) = 1)
    (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1}) :
    (s - 1 + 2 ^ (a - s + 1)) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hq : 2 ≤ 2 ^ (a - s + 1) := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
      (show 1 ≤ a - s + 1 by omega)
  have hpow : 2 ^ (a - s + 1) * 2 ^ (s - 1) = 2 ^ a := by
    rw [← pow_add]
    congr 1
    omega
  have hb := cyclic_count_ge_of_top_root_bounds (c := 2 ^ (a - s + 1) - 2) hs hm
    (orderOf_dvd_of_sylow_exponent_bound Nat.prime_two P hP hcard hsa)
    (fun e he => hbase e (he.trans (by
      rw [hcard]
      exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 hsa) m))) (by
      intro d hd
      rw [Nat.sub_add_cancel hq, ← mul_assoc, hpow]
      exact root_lower_bound_of_sylow_exponent_bound Nat.prime_two P hP
        hcard hbase hd le_rfl hsa)
  convert hb using 1
  congr 1
  omega

theorem sylow_card_eq_two_part
    {G : Type*} [Group G] [Finite G] {a m : ℕ} (P : Sylow 2 G)
    (hm : Odd m) (hcard : Nat.card G = 2 ^ a * m) : Nat.card P = 2 ^ a := by
  rw [P.card_eq_multiplicity, hcard,
    Nat.factorization_mul (by positivity) hm.pos.ne']
  simp [Nat.prime_two.factorization_pow,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat]

/-- Noncyclic Sylow subgroups give `(a+2) τ(m)` using ordinary root bounds. -/
theorem cyclic_count_ge_of_noncyclic_sylow
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1}) :
    (a + 2) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hPc : Nat.card P = 2 ^ ((a - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact sylow_card_eq_two_part P hm hcard
  have hP := AmiriNext.pow_eq_one_of_prime_power_card_not_cyclic
    Nat.prime_two hPc hnc
  have h := cyclic_count_ge_of_sylow_exponent_bound (s := a - 1)
    (by omega) (by omega) hm P hP hcard hbase
  have he : a - (a - 1) + 1 = 2 := by omega
  simpa only [he, show (2 : ℕ) ^ 2 = 4 by norm_num,
    show a - 1 - 1 + 4 = a + 2 by omega] using h

/-- Under the actual strict FC threshold, an ordinary Frobenius lower bound
already forces the 2-part exponent to be at most five. -/
theorem two_part_le_five_of_noncyclic_sylow
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : Conjecture55Lean4Web.cyc G <
      2 ^ (Conjecture55Lean4Web.numPrimeFactors G + 2)) : a ≤ 5 := by
  by_contra h
  have hcount := cyclic_count_ge_of_noncyclic_sylow ha hm P hnc hcard hbase
  have hcount8 : 8 * m.divisors.card ≤ Conjecture55Lean4Web.cyc G :=
    (Nat.mul_le_mul_right _ (by omega : 8 ≤ a + 2)).trans hcount
  exact Nat.not_lt_of_ge
    (Conjecture55RootShape.threshold_le_of_eight_mul_divisor_count
      a m (by omega) hm hcard hcount8) hlt

/-- A second exponent drop is impossible below the FC threshold. This gives
an actual element generating a cyclic subgroup of index two in the Sylow group. -/
theorem exists_order_half_sylow_card_of_strict_fc_bound
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 3 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : Conjecture55Lean4Web.cyc G <
      2 ^ (Conjecture55Lean4Web.numPrimeFactors G + 2)) :
    ∃ x : P, orderOf x = 2 ^ (a - 1) := by
  by_contra h
  push Not at h
  have hPc := sylow_card_eq_two_part P hm hcard
  have hP : ∀ x : P, x ^ (2 ^ (a - 2)) = 1 := by
    intro x
    have hd : orderOf x ∣ 2 ^ a := hPc ▸ orderOf_dvd_natCard x
    obtain ⟨k, hka, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hkne : k ≠ a := by
      intro hka'
      apply hnc
      exact isCyclic_of_orderOf_eq_card x (by rw [hk, hka', hPc])
    have hkne' : k ≠ a - 1 := by
      intro hka'
      exact h x (by rw [hk, hka'])
    exact orderOf_dvd_iff_pow_eq_one.mp (hk ▸ pow_dvd_pow 2 (by omega))
  have hcount := cyclic_count_ge_of_sylow_exponent_bound (s := a - 2)
    (by omega) (by omega) hm P hP hcard hbase
  have he : a - (a - 2) + 1 = 3 := by omega
  have hcount' : (a + 5) * m.divisors.card ≤ Conjecture55Lean4Web.cyc G := by
    change (a + 5) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G)
    simpa only [he, show (2 : ℕ) ^ 3 = 8 by norm_num,
      show a - 2 - 1 + 8 = a + 5 by omega] using hcount
  have hcount8 : 8 * m.divisors.card ≤ Conjecture55Lean4Web.cyc G :=
    (Nat.mul_le_mul_right _ (by omega : 8 ≤ a + 5)).trans hcount'
  exact Nat.not_lt_of_ge
    (Conjecture55RootShape.threshold_le_of_eight_mul_divisor_count
      a m (by omega) hm hcard hcount8) hlt

theorem exists_cyclic_index_two_of_strict_fc_bound
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 3 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : Conjecture55Lean4Web.cyc G <
      2 ^ (Conjecture55Lean4Web.numPrimeFactors G + 2)) :
    ∃ C : Subgroup P, IsCyclic C ∧ C.index = 2 := by
  obtain ⟨x, hx⟩ := exists_order_half_sylow_card_of_strict_fc_bound
    ha hm P hnc hcard hbase hlt
  refine ⟨Subgroup.zpowers x, inferInstance, ?_⟩
  have hc := (Subgroup.zpowers x).card_mul_index
  rw [Nat.card_zpowers, hx] at hc
  have hPc : Nat.card P = 2 ^ a := sylow_card_eq_two_part P hm hcard
  have hc' : 2 ^ (a - 1) * (Subgroup.zpowers x).index = 2 ^ a := hc.trans hPc
  have hpow : 2 ^ a = 2 ^ (a - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hpow] at hc'
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (a - 1)) hc'

end
end RootWeights
end

/-! ### Module `FTOnly.Large` -/
section
/-! Sylow 2-subgroups of order at least sixteen.  The three normalized cyclic
subgroups of orders two, four and eight need only a nonabelian simple normal
subgroup with trivial centralizer; they need not lie in it. -/

namespace C55FT
open Conjecture55Lean4Web Conjecture55PartialCount Conjecture55ConjugateOdd
open Conjecture55ThreeFamilies Conjecture55OddSquarefree Conjecture55Lean4Web.CyclicSum

/-- An element of order `2 ^ (a - 1)` in a Sylow subgroup of order `2 ^ a`
generates a subgroup of index two. -/
theorem zpowers_index_eq_two {G : Type*} [Group G] [Finite G] {a m : ℕ}
    (ha : 1 ≤ a) (hm : Odd m) (hcard : Nat.card G = 2 ^ a * m) (P : Sylow 2 G)
    (x : P) (hx : orderOf x = 2 ^ (a - 1)) : (Subgroup.zpowers x).index = 2 := by
  have hPc : Nat.card P = 2 ^ a := RootWeights.sylow_card_eq_two_part P hm hcard
  have hc := (Subgroup.zpowers x).card_mul_index
  change _ * _ = Nat.card P at hc
  rw [Nat.card_zpowers, hx, hPc] at hc
  have h2a : 2 ^ a = 2 ^ (a - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2a] at hc
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hc

theorem orderOf_coe_pow_two_pow {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (x : P) {k s : ℕ} (hx : orderOf x = 2 ^ k) (hs : s ≤ k) :
    orderOf ((x : G) ^ (2 ^ s)) = 2 ^ (k - s) := by
  rw [orderOf_pow, Subgroup.orderOf_coe, hx, Nat.gcd_eq_right (pow_dvd_pow 2 hs),
    Nat.pow_div hs (by norm_num)]

theorem threshold_eq {G : Type} [Group G] [Fintype G] {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ a * m) :
    2 ^ (numPrimeFactors G + 2) = 8 * 2 ^ m.primeFactors.card := by
  have hω : numPrimeFactors G = m.primeFactors.card + 1 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
    rw [hcard]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 a m Nat.prime_two ha hm.pos
      hm.not_two_dvd_nat
  rw [hω, show m.primeFactors.card + 1 + 2 = m.primeFactors.card + 3 by omega, pow_add]
  ring

/-- The large branch: `|P| ≥ 16`, so the odd part is squarefree. -/
theorem false_of_large_two_part {G : Type} [Group G] [Fintype G]
    {a m : ℕ} (ha : 4 ≤ a) (hm : Odd m) (hsf : Squarefree m)
    (hcard : Nat.card G = 2 ^ a * m) (P : Sylow 2 G) (hnc : ¬ IsCyclic P)
    (S : Subgroup G) [S.Normal] (hs : IsSimpleGroup S) (hn : ¬ IsMulCommutative S)
    (h4 : 4 ∣ Nat.card S) (hC : Subgroup.centralizer (S : Set G) = ⊥)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) : False := by
  classical
  obtain ⟨x, hx⟩ := RootWeights.exists_order_half_sylow_card_of_strict_fc_bound
    (by omega : 3 ≤ a) hm P hnc hcard (Conjecture55FrobeniusProof.rootCountLowerBound G) hlt
  have hidx := zpowers_index_eq_two (by omega) hm hcard P x hx
  have hfam (i : ℕ) (hi : i ≤ 2) :
      5 * m.divisors.card ≤ 2 * Nat.card (CyclicWithTwoPart G i) := by
    let A : Subgroup G := Subgroup.zpowers ((x : G) ^ (2 ^ (a - 2 - i)))
    have hA : Nat.card A = 2 ^ (i + 1) := by
      rw [Nat.card_zpowers, orderOf_coe_pow_two_pow (P : Subgroup G) x hx (by omega)]
      congr 1
      omega
    have hPN := le_normalizer_zpowers_pow (P : Subgroup G) x hidx (2 ^ (a - 2 - i))
    obtain ⟨c, hc, hmc, ho, hle⟩ := family_bound hm hcard P A hA hPN
    have hAbot : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hA
      have : 2 ≤ 2 ^ (i + 1) := Nat.le_self_pow (by omega) 2
      omega
    have h5 := normalizer_index_ge_five S hs hn h4 hC A hAbot ho
    have hg := normalizer_gain hsf ho h5 hmc
    omega
  have h0 := hfam 0 (by norm_num)
  have h1 := hfam 1 (by norm_num)
  have h2 := hfam 2 (by norm_num)
  have hodd := divisors_card_le_cyclicDividing (G := G) (n := m)
    (by rw [hcard]; exact dvd_mul_left _ _)
  have hsum := cyclic_count_ge_odd_and_three_families (G := G) hm
  have hexp := threshold_eq (G := G) (by omega) hm hcard
  rw [divisors_card_of_squarefree hsf] at h0 h1 h2 hodd
  have hcyc : cyc G = Nat.card (CyclicSubgroups G) := rfl
  rw [hexp, hcyc] at hlt
  omega

end C55FT
end

/-! ### Module `FTOnly.FourA` -/
section
/-! Groups whose Sylow 2-subgroup has order four and is not cyclic: basic
structure.  Burnside's transfer theorem and the odd order theorem make its three
involutions conjugate, and then every involution of the group is conjugate. -/

namespace C55FT
open Conjecture55Lean4Web Subgroup

section
variable {G : Type} [Group G] [Fintype G]

theorem isPGroup_zpowers_of_orderOf_dvd {w : G} {n : ℕ} (hw : orderOf w ∣ 2 ^ n) :
    IsPGroup 2 (zpowers w) := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hw
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

/-- No element has order four when the Sylow 2-subgroup has order four and is
not cyclic. -/
theorem orderOf_ne_four {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (x : G) : orderOf x ≠ 4 := by
  intro hx
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPc : Nat.card P = 2 ^ 2 := RootWeights.sylow_card_eq_two_part P hm hcard
  have hZc : Nat.card (zpowers x) = 2 ^ (Nat.card G).factorization 2 := by
    rw [Nat.card_zpowers, hx, ← Sylow.card_eq_multiplicity P, hPc]
    norm_num
  let Q : Sylow 2 G := Sylow.ofCard (zpowers x) hZc
  have hxQ : x ∈ (Q : Subgroup G) := by
    rw [Sylow.coe_ofCard]
    exact mem_zpowers x
  have hQc : Nat.card (Q : Subgroup G) = 4 := by
    rw [Sylow.coe_ofCard, Nat.card_zpowers, hx]
  have hQcyc : IsCyclic Q :=
    isCyclic_of_orderOf_eq_card (⟨x, hxQ⟩ : (Q : Subgroup G)) (by rw [orderOf_mk, hx, hQc])
  exact hnc (isCyclic_of_injective (P.equiv Q).toMonoidHom (P.equiv Q).injective)

theorem sq_eq_one_of_orderOf_dvd_four (hne : ∀ x : G, orderOf x ≠ 4) (x : G)
    (hx : orderOf x ∣ 4) : x ^ 2 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  have h : orderOf x ∣ 2 ^ 2 := by simpa using hx
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  interval_cases k
  · rw [hk']; norm_num
  · rw [hk']; norm_num
  · exact absurd (by rw [hk']; norm_num) (hne x)

theorem sq_eq_one_of_mem_sylow {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) {x : G} (hx : x ∈ (P : Subgroup G)) : x ^ 2 = 1 := by
  apply sq_eq_one_of_orderOf_dvd_four (orderOf_ne_four hm hcard P hnc)
  have hPc : Nat.card P = 2 ^ 2 := RootWeights.sylow_card_eq_two_part P hm hcard
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : (P : Subgroup G))
  rw [orderOf_mk] at h
  change orderOf x ∣ Nat.card P at h
  rw [hPc] at h
  simpa using h

theorem mul_comm_of_mem_sylow {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) {x y : G} (hx : x ∈ (P : Subgroup G))
    (hy : y ∈ (P : Subgroup G)) : x * y = y * x := by
  have h1 := sq_eq_one_of_mem_sylow hm hcard P hnc hx
  have h2 := sq_eq_one_of_mem_sylow hm hcard P hnc hy
  have h3 := sq_eq_one_of_mem_sylow hm hcard P hnc ((P : Subgroup G).mul_mem hx hy)
  have hxi : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one, ← sq, h1]
  have hyi : y⁻¹ = y := by rw [inv_eq_iff_mul_eq_one, ← sq, h2]
  have hxyi : (x * y)⁻¹ = x * y := by rw [inv_eq_iff_mul_eq_one, ← sq, h3]
  rw [mul_inv_rev, hxi, hyi] at hxyi
  exact hxyi.symm

/-- A 2-element normalizing the Sylow subgroup lies in it. -/
theorem mem_sylow_of_mem_normalizer {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) {w : G} (hw : IsPGroup 2 (zpowers w))
    (hN : w ∈ normalizer ((P : Subgroup G) : Set G)) : w ∈ (P : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : zpowers w ≤ normalizer ((P : Subgroup G) : Set G) := (zpowers_le).mpr hN
  have hsup : IsPGroup 2 (zpowers w ⊔ (P : Subgroup G) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hw P.isPGroup' hle
  obtain ⟨Q, hQ⟩ := hsup.exists_le_sylow
  have hc : Nat.card (zpowers w ⊔ (P : Subgroup G) : Subgroup G) ≤
      Nat.card (P : Subgroup G) := by
    calc _ ≤ Nat.card (Q : Subgroup G) := card_le_of_le hQ
      _ = Nat.card (P : Subgroup G) := by
        rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P]
  have heq := eq_of_le_of_card_ge (le_sup_right : (P : Subgroup G) ≤ _) hc
  rw [heq]
  exact mem_sup_left (mem_zpowers w)

/-- Burnside's transfer theorem, together with the odd order theorem. -/
theorem not_normalizer_le_centralizer (hFT : OddOrderTheorem) [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (P : Sylow 2 G) : ¬ normalizer P ≤ centralizer (P : Set G) := by
  intro hP
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP
  let N := (MonoidHom.transferSylow P hP).ker
  have hNc : Nat.card N = (P : Subgroup G).index := hcomp.index_eq_card.symm
  have hodd : Odd (Nat.card N) := by
    rw [hNc]
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using P.not_dvd_index)
  have hNbot : N = ⊥ := hrad N inferInstance (hFT N hodd)
  have hidx : (P : Subgroup G).index = 1 := by
    rw [← hNc, hNbot, card_bot]
  have hPtop : (P : Subgroup G) = ⊤ := index_eq_one.mp hidx
  have hGp : IsPGroup 2 G := by
    intro g
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hPtop ▸ mem_top g⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  let : Group.IsNilpotent G := hGp.isNilpotent
  exact not_solvable_of_nontrivial_radicalFree hrad inferInstance

end
end C55FT
end

/-! ### Module `FTOnly.FourB` -/
section
/-! The three involutions of the Sylow subgroup, and the conjugacy class of all
involutions of the group. -/

namespace C55FT
open Conjecture55Lean4Web Subgroup

section
variable {G : Type} [Group G] [Fintype G]

/-- A noncyclic group of order four consists of `1`, two distinct involutions,
and their product. -/
theorem eq_of_mem_sylow_four {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) {a b : G} (ha : a ∈ (P : Subgroup G))
    (hb : b ∈ (P : Subgroup G)) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ∀ x ∈ (P : Subgroup G), x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  have hPc : Nat.card P = 2 ^ 2 := RootWeights.sylow_card_eq_two_part P hm hcard
  have ha2 := sq_eq_one_of_mem_sylow hm hcard P hnc ha
  have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq, ha2]
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hb', hainv]
  have haba : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habb : a * b ≠ b := fun h => ha1 (by simpa using h)
  let F : Finset G := {1, a, b, a * b}
  have hFc : F.card = 4 := by
    simp only [F]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact habb.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, fun h => haba (h.symm)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  let PF : Finset G := Finset.univ.filter (· ∈ (P : Subgroup G))
  have hPF : PF.card = 4 := by
    have : Nat.card (P : Subgroup G) = PF.card := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp [PF]))
    change Nat.card P = 2 ^ 2 at hPc
    rw [← this, hPc]
    norm_num
  have hsub : F ⊆ PF := by
    intro x hx
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [PF, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ha
    · exact hb
    · exact mul_mem ha hb
  have heq : F = PF := Finset.eq_of_subset_of_card_le hsub (by rw [hFc, hPF])
  intro x hx
  have hxF : x ∈ F := by
    rw [heq]
    simp [PF, hx]
  simpa [F] using hxF

/-- Commuting from a conjugation fixing an element. -/
theorem commute_of_conj_eq {x y : G} (h : x * y * x⁻¹ = y) : y * x = x * y :=
  (mul_inv_eq_iff_eq_mul.mp h).symm

/-- Burnside's transfer theorem and the odd order theorem give an element of the
normalizer moving an involution `τ` to `σ` and `σ` to a third involution `ρ`. -/
theorem exists_conj_triple (hFT : OddOrderTheorem) [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m) (P : Sylow 2 G)
    (hnc : ¬ IsCyclic P) :
    ∃ τ g : G, τ ∈ (P : Subgroup G) ∧ g ∈ normalizer ((P : Subgroup G) : Set G) ∧ τ ≠ 1 ∧
      g * τ * g⁻¹ ≠ τ ∧ g * (g * τ * g⁻¹) * g⁻¹ ≠ τ ∧
      g * (g * τ * g⁻¹) * g⁻¹ ≠ g * τ * g⁻¹ := by
  classical
  have hNC := not_normalizer_le_centralizer hFT hrad P
  obtain ⟨h, hhN, hhC⟩ := IsConcreteLE.not_le_iff_exists.mp hNC
  obtain ⟨s, r, hr, hd⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  let h2 := h ^ r
  let g := h ^ (2 ^ s)
  have hh2N : h2 ∈ normalizer ((P : Subgroup G) : Set G) := pow_mem hhN r
  have hgN : g ∈ normalizer ((P : Subgroup G) : Set G) := pow_mem hhN _
  have hh2p : IsPGroup 2 (zpowers h2) := isPGroup_zpowers_of_orderOf_dvd (n := s) (by
    apply orderOf_dvd_of_pow_eq_one
    simp only [h2]
    rw [← pow_mul, mul_comm, ← hd, pow_orderOf_eq_one])
  have hh2P : h2 ∈ (P : Subgroup G) := mem_sylow_of_mem_normalizer hm hcard P hh2p hh2N
  have hgr : g ^ r = 1 := by
    simp only [g]
    rw [← pow_mul, ← hd, pow_orderOf_eq_one]
  have hPC : ∀ y ∈ (P : Subgroup G), ∀ z ∈ (P : Subgroup G), y * z = z * y :=
    fun y hy z hz => mul_comm_of_mem_sylow hm hcard P hnc hy hz
  have hgC : g ∉ centralizer ((P : Subgroup G) : Set G) := by
    intro hgC
    apply hhC
    have hcop : Nat.Coprime (2 ^ s) r :=
      Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hr)
    have hexp : ((2 ^ s : ℕ) : ℤ) * Nat.gcdA (2 ^ s) r + (r : ℤ) * Nat.gcdB (2 ^ s) r = 1 := by
      have := Nat.gcd_eq_gcd_ab (2 ^ s) r
      rw [hcop.gcd_eq_one] at this
      simpa using this.symm
    have hh : h = g ^ (Nat.gcdA (2 ^ s) r) * h2 ^ (Nat.gcdB (2 ^ s) r) := by
      simp only [g, h2]
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, hexp, zpow_one]
    rw [hh]
    have hh2C : h2 ∈ centralizer ((P : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact hPC y hy h2 hh2P
    exact mul_mem (zpow_mem hgC _) (zpow_mem hh2C _)
  have hmove : ∃ τ ∈ (P : Subgroup G), g * τ * g⁻¹ ≠ τ := by
    by_contra hcon
    push Not at hcon
    apply hgC
    rw [mem_centralizer_iff]
    intro y hy
    exact commute_of_conj_eq (hcon y hy)
  obtain ⟨τ, hτP, hτ⟩ := hmove
  let σ := g * τ * g⁻¹
  let ρ := g * σ * g⁻¹
  have hσP : σ ∈ (P : Subgroup G) := (mem_normalizer_iff.mp hgN τ).mp hτP
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    simp at hτ
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hτ1
    have : g * τ * g⁻¹ = g * 1 * g⁻¹ := by rw [mul_one, mul_inv_cancel]; exact h
    simpa using this
  have hρσ : ρ ≠ σ := by
    intro h
    apply hτ
    have h' : g * σ * g⁻¹ = g * τ * g⁻¹ := h
    have : σ = τ := by simpa using h'
    exact this
  have hρτ : ρ ≠ τ := by
    intro hρ
    have hτσ : τ ≠ σ := fun h => hτ h.symm
    have hall := eq_of_mem_sylow_four hm hcard P hnc hτP hσP hτ1 hσ1 hτσ
    have hg2τ : g ^ 2 * τ * (g ^ 2)⁻¹ = τ := by
      calc g ^ 2 * τ * (g ^ 2)⁻¹ = g * (g * τ * g⁻¹) * g⁻¹ := by rw [pow_two]; group
        _ = τ := hρ
    have hg2σ : g ^ 2 * σ * (g ^ 2)⁻¹ = σ := by
      calc g ^ 2 * σ * (g ^ 2)⁻¹ = g * (g * σ * g⁻¹) * g⁻¹ := by rw [pow_two]; group
        _ = g * ρ * g⁻¹ := rfl
        _ = g * τ * g⁻¹ := by rw [hρ]
    have hg2C : g ^ 2 ∈ centralizer ((P : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      rcases hall y hy with rfl | rfl | rfl | rfl
      · simp
      · exact commute_of_conj_eq hg2τ
      · exact commute_of_conj_eq hg2σ
      · have h1 := commute_of_conj_eq hg2τ
        have h2' := commute_of_conj_eq hg2σ
        rw [mul_assoc, h2', ← mul_assoc, h1, mul_assoc]
    apply hgC
    have hgodd : g = (g ^ 2) ^ ((r + 1) / 2) := by
      rw [← pow_mul]
      have h2r : 2 * ((r + 1) / 2) = r + 1 := by
        obtain ⟨k, hk⟩ := hr
        omega
      rw [h2r, pow_succ, hgr, one_mul]
    rw [hgodd]
    exact pow_mem hg2C _
  exact ⟨τ, g, hτP, hgN, hτ1, hτ, hρτ, hρσ⟩

/-- Every involution is conjugate to `τ`. -/
theorem exists_conj_of_involution {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) {τ g : G} (hτP : τ ∈ (P : Subgroup G))
    (hgN : g ∈ normalizer ((P : Subgroup G) : Set G)) (hτ1 : τ ≠ 1)
    (hσ : g * τ * g⁻¹ ≠ τ) (hρτ : g * (g * τ * g⁻¹) * g⁻¹ ≠ τ)
    (hρσ : g * (g * τ * g⁻¹) * g⁻¹ ≠ g * τ * g⁻¹)
    {w : G} (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) : ∃ x : G, x * τ * x⁻¹ = w := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ := g * τ * g⁻¹
  let ρ := g * σ * g⁻¹
  have hσP : σ ∈ (P : Subgroup G) := (mem_normalizer_iff.mp hgN τ).mp hτP
  have hρP : ρ ∈ (P : Subgroup G) := (mem_normalizer_iff.mp hgN σ).mp hσP
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hτ1
    have : g * τ * g⁻¹ = g * 1 * g⁻¹ := by rw [mul_one, mul_inv_cancel]; exact h
    simpa using this
  have hρ1 : ρ ≠ 1 := by
    intro h
    apply hσ1
    have : g * σ * g⁻¹ = g * 1 * g⁻¹ := by rw [mul_one, mul_inv_cancel]; exact h
    simpa using this
  have hτσ : τ ≠ σ := fun h => hσ h.symm
  have hall := eq_of_mem_sylow_four hm hcard P hnc hτP hσP hτ1 hσ1 hτσ
  have hρ' : ρ = τ * σ := by
    rcases hall ρ hρP with h | h | h | h
    · exact absurd h hρ1
    · exact absurd h hρτ
    · exact absurd h hρσ
    · exact h
  have hwp : IsPGroup 2 (zpowers w) := isPGroup_zpowers_of_orderOf_dvd (n := 1)
    (by simpa using orderOf_dvd_of_pow_eq_one hw2)
  obtain ⟨Q, hQ⟩ := hwp.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G P Q
  have hwQ : w ∈ (Q : Subgroup G) := hQ (mem_zpowers w)
  rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hwQ
  obtain ⟨p, hp, hpw⟩ := hwQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hpw
  have hp1 : p ≠ 1 := by
    rintro rfl
    apply hw1
    rw [← hpw]
    group
  rcases hall p hp with h | h | h | h
  · exact absurd h hp1
  · exact ⟨y, by rw [← hpw, h]⟩
  · exact ⟨y * g, by rw [← hpw, h]; simp only [σ]; group⟩
  · exact ⟨y * g * g, by rw [← hpw, h, ← hρ']; simp only [ρ, σ]; group⟩

/-- The involutions of `G`. -/
def invFinset (G : Type) [Group G] [Fintype G] [DecidableEq G] : Finset G :=
  Finset.univ.filter (fun w => w ^ 2 = 1 ∧ w ≠ 1)

theorem card_invFinset_eq_index [DecidableEq G] {τ : G} (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hconj : ∀ w : G, w ^ 2 = 1 → w ≠ 1 → ∃ x : G, x * τ * x⁻¹ = w) :
    (invFinset G).card = (centralizer ({τ} : Set G)).index := by
  rw [Subgroup.index_centralizer_eq_ncard]
  have hset : conjugatesOf τ = ((invFinset G : Finset G) : Set G) := by
    ext w
    simp only [conjugatesOf, Set.mem_setOf_eq, invFinset, Finset.coe_filter,
      Finset.mem_univ, true_and, isConj_iff]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨by rw [conj_pow, hτ2]; group, ?_⟩
      intro h
      apply hτ1
      have : c * τ * c⁻¹ = c * 1 * c⁻¹ := by rw [h]; group
      simpa using this
    · rintro ⟨hw2, hw1⟩
      exact hconj w hw2 hw1
  rw [hset, Set.ncard_coe_finset]

theorem normalizer_zpowers_eq_centralizer {τ : G} (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1) :
    normalizer ((zpowers τ : Subgroup G) : Set G) = centralizer ({τ} : Set G) := by
  have hz : ∀ x ∈ zpowers τ, x = 1 ∨ x = τ := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have h2' : τ ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hτ2]
    rcases Int.even_or_odd' k with ⟨t, rfl | rfl⟩
    · left
      rw [zpow_mul, h2', one_zpow]
    · right
      rw [zpow_add, zpow_mul, h2', one_zpow, one_mul, zpow_one]
  ext x
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have h := (mem_normalizer_iff.mp hx τ).mp (mem_zpowers τ)
    rcases hz _ h with h1 | h1
    · exfalso
      apply hτ1
      have : x * τ * x⁻¹ = x * 1 * x⁻¹ := by rw [h1]; group
      simpa using this
    · exact (commute_of_conj_eq h1).symm
  · intro hx
    rw [mem_normalizer_iff]
    intro y
    have hconj : ∀ z : G, z ∈ zpowers τ → x * z * x⁻¹ = z := by
      intro z hz'
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz'
      rw [← conj_zpow, show x * τ * x⁻¹ = τ by rw [hx]; group]
    constructor
    · intro hy
      rw [hconj y hy]
      exact hy
    · intro hy
      have := hconj _ hy
      have hyy : y = x * y * x⁻¹ := by
        have h' : x * (x * y * x⁻¹) * x⁻¹ = x * y * x⁻¹ := this
        have : x * y * x⁻¹ = y := by simpa using h'
        exact this.symm
      rw [hyy]
      exact hy

end
end C55FT
end

/-! ### Module `FTOnly.FourC` -/
section
/-! In the centralizer of an involution `τ` of `P`, every Sylow 2-subgroup is a
Klein four group containing `τ`, and two of them meet only in `⟨τ⟩`.  Hence the
involutions commuting with `τ` number `1 + 2 j`, where `j` is the number of
Sylow 2-subgroups of the centralizer. -/

namespace C55FT
open Conjecture55Lean4Web Subgroup

section
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

theorem natCard_subgroup_eq_filter (H : Subgroup G) [DecidablePred (· ∈ H)] :
    Nat.card H = (Finset.univ.filter (· ∈ H)).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]

theorem le_centralizer_of_sylow_four {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) {τ : G} (hτP : τ ∈ (P : Subgroup G)) :
    (P : Subgroup G) ≤ centralizer ({τ} : Set G) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact mul_comm_of_mem_sylow hm hcard P hnc hx hτP

theorem card_commute_eq_one_add_two_mul {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) {τ : G} (hτP : τ ∈ (P : Subgroup G)) (hτ1 : τ ≠ 1) :
    ((invFinset G).filter (fun w => w * τ = τ * w)).card =
      1 + 2 * Nat.card (Sylow 2 (centralizer ({τ} : Set G))) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer ({τ} : Set G)
  let : Fintype (Sylow 2 C) := Fintype.ofFinite _
  have hPC : (P : Subgroup G) ≤ C := le_centralizer_of_sylow_four hm hcard P hnc hτP
  obtain ⟨-, c, hc, -, hCc⟩ := Conjecture55ThreeFamilies.factor_of_sylow_le hm hcard P C hPC
  have hne := orderOf_ne_four hm hcard P hnc
  have hτ2 : τ ^ 2 = 1 := sq_eq_one_of_mem_sylow hm hcard P hnc hτP
  have hτC : τ ∈ C := by
    change τ ∈ centralizer ({τ} : Set G)
    rw [mem_centralizer_singleton_iff]
  let τ' : C := ⟨τ, hτC⟩
  have hQc (Q : Sylow 2 C) : Nat.card Q = 2 ^ 2 := RootWeights.sylow_card_eq_two_part Q hc hCc
  let img (Q : Sylow 2 C) : Subgroup G := (Q : Subgroup C).map C.subtype
  have himgc (Q : Sylow 2 C) : Nat.card (img Q) = 4 := by
    simp only [img]
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    have := hQc Q
    change Nat.card (Q : Subgroup C) = 2 ^ 2 at this
    rw [this]
    norm_num
  have himgC (Q : Sylow 2 C) : img Q ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hτQ (Q : Sylow 2 C) : τ' ∈ (Q : Subgroup C) := by
    have hcent : ∀ x : C, τ' * x = x * τ' := by
      intro x
      apply Subtype.ext
      have := x.2
      change (x : G) ∈ centralizer ({τ} : Set G) at this
      rw [mem_centralizer_singleton_iff] at this
      exact this.symm
    have hN : zpowers τ' ≤ normalizer ((Q : Subgroup C) : Set C) := by
      rw [zpowers_le, mem_normalizer_iff]
      intro h
      rw [hcent h, mul_inv_cancel_right]
    have hp : IsPGroup 2 (zpowers τ') := isPGroup_zpowers_of_orderOf_dvd (n := 1) (by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa using hτ2)
    have hsup := IsPGroup.to_sup_of_normal_right' hp Q.isPGroup' hN
    have heq := Q.is_maximal' hsup le_sup_right
    rw [← heq]
    exact mem_sup_left (mem_zpowers τ')
  have hτimg (Q : Sylow 2 C) : τ ∈ img Q := ⟨τ', hτQ Q, rfl⟩
  have hsq (Q : Sylow 2 C) (w : G) (hw : w ∈ img Q) : w ^ 2 = 1 := by
    apply sq_eq_one_of_orderOf_dvd_four hne
    have h := orderOf_dvd_natCard (⟨w, hw⟩ : img Q)
    rw [orderOf_mk, himgc] at h
    exact h
  let B (Q : Sylow 2 C) : Finset G := (Finset.univ.filter (· ∈ img Q)) \ {1, τ}
  have hBc (Q : Sylow 2 C) : (B Q).card = 2 := by
    have hA : (Finset.univ.filter (· ∈ img Q)).card = 4 := by
      rw [← natCard_subgroup_eq_filter, himgc]
    have hsub : ({1, τ} : Finset G) ⊆ Finset.univ.filter (· ∈ img Q) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl
      · exact one_mem _
      · exact hτimg Q
    simp only [B]
    rw [Finset.card_sdiff_of_subset hsub, hA, Finset.card_pair (Ne.symm hτ1)]
  have hdisj : ∀ Q ∈ (Finset.univ : Finset (Sylow 2 C)), ∀ Q' ∈ (Finset.univ : Finset (Sylow 2 C)),
      Q ≠ Q' → Disjoint (B Q) (B Q') := by
    intro Q _ Q' _ hQQ
    rw [Finset.disjoint_left]
    intro w hwQ hwQ'
    simp only [B, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hwQ hwQ'
    apply hQQ
    have hsub3 : ({1, τ, w} : Finset G) ⊆ Finset.univ.filter (· ∈ (img Q ⊓ img Q' : Subgroup G)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf]
      rcases hx with rfl | rfl | rfl
      · exact ⟨one_mem _, one_mem _⟩
      · exact ⟨hτimg Q, hτimg Q'⟩
      · exact ⟨hwQ.1, hwQ'.1⟩
    have h3 : ({1, τ, w} : Finset G).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (fun h => hwQ.2.2 h.symm)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hτ1, fun h => hwQ.2.1 h.symm⟩
    have hge : 3 ≤ Nat.card (img Q ⊓ img Q' : Subgroup G) := by
      rw [natCard_subgroup_eq_filter, ← h3]
      exact Finset.card_le_card hsub3
    have hdvd : Nat.card (img Q ⊓ img Q' : Subgroup G) ∣ 4 := by
      rw [← himgc Q]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hinf : Nat.card (img Q ⊓ img Q' : Subgroup G) = 4 := by
      rcases (by omega : Nat.card (img Q ⊓ img Q' : Subgroup G) = 3 ∨
          Nat.card (img Q ⊓ img Q' : Subgroup G) = 4) with h | h
      · rw [h] at hdvd
        norm_num at hdvd
      · exact h
    have e1 : img Q ⊓ img Q' = img Q := eq_of_le_of_card_ge inf_le_left (by rw [hinf, himgc])
    have e2 : img Q ⊓ img Q' = img Q' := eq_of_le_of_card_ge inf_le_right (by rw [hinf, himgc])
    exact Sylow.ext (Subgroup.map_injective C.subtype_injective (e1.symm.trans e2))
  have hunion : (Finset.univ : Finset (Sylow 2 C)).biUnion B =
      ((invFinset G).filter (fun w => w * τ = τ * w)).erase τ := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, B, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, not_or, Finset.mem_erase,
      invFinset]
    constructor
    · rintro ⟨Q, hwQ, hw1, hwτ⟩
      refine ⟨hwτ, ⟨hsq Q w hwQ, hw1⟩, ?_⟩
      have h := himgC Q hwQ
      change w ∈ centralizer ({τ} : Set G) at h
      rw [mem_centralizer_singleton_iff] at h
      exact h
    · rintro ⟨hwτ, ⟨hw2, hw1⟩, hwc⟩
      have hwC : w ∈ C := by
        change w ∈ centralizer ({τ} : Set G)
        rw [mem_centralizer_singleton_iff]
        exact hwc
      let w' : C := ⟨w, hwC⟩
      have hp : IsPGroup 2 (zpowers w') := isPGroup_zpowers_of_orderOf_dvd (n := 1) (by
        apply orderOf_dvd_of_pow_eq_one
        apply Subtype.ext
        simpa using hw2)
      obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
      exact ⟨Q, ⟨w', hQ (mem_zpowers w'), rfl⟩, hw1, hwτ⟩
  have hcardU : ((Finset.univ : Finset (Sylow 2 C)).biUnion B).card =
      2 * Nat.card (Sylow 2 C) := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun Q _ => hBc Q), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]
  have hτmem : τ ∈ (invFinset G).filter (fun w => w * τ = τ * w) := by
    simp [invFinset, hτ2, hτ1]
  rw [← Finset.card_erase_add_one hτmem, ← hunion, hcardU]
  ring

end
end C55FT
end

/-! ### Module `FTOnly.FourD` -/
section
/-! The Klein four Sylow subgroup `T = {1, τ, σ, ρ}` acts by conjugation on the
involutions outside `T`.  The fixed points of `τ`, `σ`, `ρ` form three disjoint
sets of the same size `f - 3`, and Burnside's lemma gives a congruence mod four. -/

namespace C55FT
open Conjecture55Lean4Web Subgroup

section
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- Conjugation does not change the number of involutions commuting with an element. -/
theorem card_commute_conj (x τ : G) :
    ((invFinset G).filter (fun w => w * (x * τ * x⁻¹) = (x * τ * x⁻¹) * w)).card =
      ((invFinset G).filter (fun w => w * τ = τ * w)).card := by
  symm
  apply Finset.card_bij (fun w _ => x * w * x⁻¹)
  · intro w hw
    simp only [invFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨⟨hw2, hw1⟩, hwc⟩ := hw
    refine ⟨⟨by rw [conj_pow, hw2]; group, ?_⟩, ?_⟩
    · intro h
      apply hw1
      have : x * w * x⁻¹ = x * 1 * x⁻¹ := by rw [h]; group
      simpa using this
    · calc x * w * x⁻¹ * (x * τ * x⁻¹) = x * (w * τ) * x⁻¹ := by group
        _ = x * (τ * w) * x⁻¹ := by rw [hwc]
        _ = x * τ * x⁻¹ * (x * w * x⁻¹) := by group
  · intro a _ b _ h
    simpa using h
  · intro w hw
    refine ⟨x⁻¹ * w * x, ?_, by group⟩
    simp only [invFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨⟨hw2, hw1⟩, hwc⟩ := hw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [show x⁻¹ * w * x = x⁻¹ * w * x⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv, hw2]
      group
    · intro h
      apply hw1
      calc w = x * (x⁻¹ * w * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
    · calc x⁻¹ * w * x * τ = x⁻¹ * (w * (x * τ * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * τ * x⁻¹) * w) * x := by rw [hwc]
        _ = τ * (x⁻¹ * w * x) := by group

/-- The constraints on `i = #involutions` and `f = #involutions commuting with τ`:
writing `i = a + 3` and `f = b + 3`, the three fixed-point sets outside `T` are
disjoint (`3 b ≤ a`) and Burnside's lemma gives `4 ∣ a + 3 b`. -/
theorem involution_constraints {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) {τ g : G} (hτP : τ ∈ (P : Subgroup G))
    (hgN : g ∈ normalizer ((P : Subgroup G) : Set G)) (hτ1 : τ ≠ 1)
    (hσ : g * τ * g⁻¹ ≠ τ) (hρτ : g * (g * τ * g⁻¹) * g⁻¹ ≠ τ)
    (hρσ : g * (g * τ * g⁻¹) * g⁻¹ ≠ g * τ * g⁻¹) :
    ∃ a b, (invFinset G).card = a + 3 ∧
      ((invFinset G).filter (fun w => w * τ = τ * w)).card = b + 3 ∧
      3 * b ≤ a ∧ 4 ∣ a + 3 * b := by
  classical
  let T : Subgroup G := (P : Subgroup G)
  let σ := g * τ * g⁻¹
  let ρ := g * σ * g⁻¹
  have hσP : σ ∈ T := (mem_normalizer_iff.mp hgN τ).mp hτP
  have hρP : ρ ∈ T := (mem_normalizer_iff.mp hgN σ).mp hσP
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hτ1
    have : g * τ * g⁻¹ = g * 1 * g⁻¹ := by rw [mul_one, mul_inv_cancel]; exact h
    simpa using this
  have hρ1 : ρ ≠ 1 := by
    intro h
    apply hσ1
    have : g * σ * g⁻¹ = g * 1 * g⁻¹ := by rw [mul_one, mul_inv_cancel]; exact h
    simpa using this
  have hτσ : τ ≠ σ := fun h => hσ h.symm
  have hall := eq_of_mem_sylow_four hm hcard P hnc hτP hσP hτ1 hσ1 hτσ
  have hρ' : ρ = τ * σ := by
    rcases hall ρ hρP with h | h | h | h
    · exact absurd h hρ1
    · exact absurd h hρτ
    · exact absurd h hρσ
    · exact h
  have hTmem : ∀ x, x ∈ T ↔ x = 1 ∨ x = τ ∨ x = σ ∨ x = ρ := by
    intro x
    constructor
    · intro hx
      rcases hall x hx with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (h.trans hρ'.symm)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact one_mem _
      · exact hτP
      · exact hσP
      · exact hρP
  have hsqT : ∀ x ∈ T, x ^ 2 = 1 := fun x hx => sq_eq_one_of_mem_sylow hm hcard P hnc hx
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x :=
    fun x hx y hy => mul_comm_of_mem_sylow hm hcard P hnc hx hy
  set f := ((invFinset G).filter (fun w => w * τ = τ * w)).card with hfdef
  have hfσ : ((invFinset G).filter (fun w => w * σ = σ * w)).card = f := card_commute_conj g τ
  have hfρ : ((invFinset G).filter (fun w => w * ρ = ρ * w)).card = f := by
    have : ρ = (g * g) * τ * (g * g)⁻¹ := by simp only [ρ, σ]; group
    rw [this]
    exact card_commute_conj (g * g) τ
  -- The involutions inside `T`.
  have hinvT : (invFinset G).filter (· ∈ T) = {τ, σ, ρ} := by
    ext x
    simp only [invFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx1⟩, hxT⟩
      rcases (hTmem x).mp hxT with h | h | h | h
      · exact absurd h hx1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨hsqT _ hτP, hτ1⟩, hτP⟩
      · exact ⟨⟨hsqT _ hσP, hσ1⟩, hσP⟩
      · exact ⟨⟨hsqT _ hρP, hρ1⟩, hρP⟩
  have hinvT3 : ((invFinset G).filter (· ∈ T)).card = 3 := by
    rw [hinvT, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hρσ)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hτσ, Ne.symm hρτ⟩
  -- Fixed points outside `T`.
  let A (u : G) := ((invFinset G).filter (· ∉ T)).filter (fun w => w * u = u * w)
  have hAcard (u : G) (hu : u ∈ T) :
      (A u).card + 3 = ((invFinset G).filter (fun w => w * u = u * w)).card := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (invFinset G).filter (fun w => w * u = u * w)) (fun w => w ∈ T)
    have h2 : ((invFinset G).filter (fun w => w * u = u * w)).filter (· ∈ T) =
        (invFinset G).filter (· ∈ T) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx, -⟩, hxT⟩
        exact ⟨hx, hxT⟩
      · rintro ⟨hx, hxT⟩
        exact ⟨⟨hx, hTcomm x hxT u hu⟩, hxT⟩
    have h3 : ((invFinset G).filter (fun w => w * u = u * w)).filter (fun w => ¬ w ∈ T) =
        A u := by
      ext x
      simp only [A, Finset.mem_filter]
      tauto
    rw [h2, hinvT3, h3] at h1
    omega
  let I' := (invFinset G).filter (· ∉ T)
  have hI'card : I'.card + 3 = (invFinset G).card := by
    have h := Finset.card_filter_add_card_filter_not (s := invFinset G) (fun w => w ∈ T)
    rw [hinvT3] at h
    change 3 + I'.card = (invFinset G).card at h
    omega
  -- Disjointness of the three fixed-point sets.
  have hdisj : ∀ u ∈ T, ∀ v ∈ T, u ≠ 1 → v ≠ 1 → u ≠ v → Disjoint (A u) (A v) := by
    intro u hu v hv hu1 hv1 huv
    rw [Finset.disjoint_left]
    intro w hwu hwv
    simp only [A, invFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hwu hwv
    obtain ⟨⟨⟨hw2, -⟩, hwT⟩, hwuc⟩ := hwu
    obtain ⟨-, hwvc⟩ := hwv
    have hallT := eq_of_mem_sylow_four hm hcard P hnc hu hv hu1 hv1 huv
    have hcx : ∀ x ∈ T, w * x = x * w := by
      intro x hx
      rcases hallT x hx with rfl | rfl | rfl | rfl
      · simp
      · exact hwuc
      · exact hwvc
      · rw [← mul_assoc, hwuc, mul_assoc, hwvc, mul_assoc]
    have hwinv : w⁻¹ = w := by rw [inv_eq_iff_mul_eq_one, ← sq, hw2]
    have hwN : w ∈ normalizer ((T : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [hcx x hx, mul_inv_cancel_right]
        exact hx
      · intro hx
        have h' := hcx _ hx
        have : x = w * x * w⁻¹ := by
          calc x = w * w * x * (w * w) := by rw [← sq, hw2]; group
            _ = w * (w * x * w⁻¹) * w⁻¹ := by rw [hwinv]; group
            _ = w * x * w⁻¹ := by rw [h', mul_inv_cancel_right]
        rw [this]
        exact hx
    have hwp : IsPGroup 2 (zpowers w) := isPGroup_zpowers_of_orderOf_dvd (n := 1)
      (by simpa using orderOf_dvd_of_pow_eq_one hw2)
    exact hwT (mem_sylow_of_mem_normalizer hm hcard P hwp hwN)
  have hsub : A τ ∪ A σ ∪ A ρ ⊆ I' := by
    intro w hw
    simp only [A, I', Finset.mem_union, Finset.mem_filter] at hw ⊢
    tauto
  have hunion : (A τ ∪ A σ ∪ A ρ).card = (A τ).card + (A σ).card + (A ρ).card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
        ⟨hdisj τ hτP ρ hρP hτ1 hρ1 (Ne.symm hρτ), hdisj σ hσP ρ hρP hσ1 hρ1 (Ne.symm hρσ)⟩),
      Finset.card_union_of_disjoint (hdisj τ hτP σ hσP hτ1 hσ1 hτσ)]
  have hle := Finset.card_le_card hsub
  have hAτ := hAcard τ hτP
  have hAσ := hAcard σ hσP
  have hAρ := hAcard ρ hρP
  rw [hfσ] at hAσ
  rw [hfρ] at hAρ
  -- Burnside's lemma for the conjugation action of `T` on `I'`.
  have hconjI' : ∀ u ∈ T, ∀ w ∈ I', u * w * u⁻¹ ∈ I' := by
    intro u hu w hw
    simp only [I', invFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨⟨hw2, hw1⟩, hwT⟩ := hw
    refine ⟨⟨by rw [conj_pow, hw2]; group, ?_⟩, ?_⟩
    · intro h
      apply hw1
      have : u * w * u⁻¹ = u * 1 * u⁻¹ := by rw [h]; group
      simpa using this
    · intro h
      apply hwT
      have : w = u⁻¹ * (u * w * u⁻¹) * u := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hu) h) hu
  let Y := {w : G // w ∈ I'}
  let act : MulAction T Y :=
    { smul := fun u y => ⟨(u : G) * y * (u : G)⁻¹, hconjI' u u.2 y y.2⟩
      one_smul := fun y => Subtype.ext (show ((1 : T) : G) * y.1 * ((1 : T) : G)⁻¹ = y.1 by simp)
      mul_smul := fun u v y => Subtype.ext (show ((u * v : T) : G) * y.1 * ((u * v : T) : G)⁻¹ =
          (u : G) * ((v : G) * y.1 * (v : G)⁻¹) * (u : G)⁻¹ by
        simp only [Subgroup.coe_mul]; group) }
  let : ∀ u : T, Fintype (MulAction.fixedBy Y u) := fun u => Fintype.ofFinite _
  let : Fintype (Quotient (MulAction.orbitRel T Y)) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group T Y
  have hfix (u : T) : Fintype.card (MulAction.fixedBy Y u) =
      (I'.filter (fun w => w * (u : G) = (u : G) * w)).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact
      { toFun := fun y => ⟨y.1.1, by
          have hy := y.2
          change (⟨(u : G) * y.1.1 * (u : G)⁻¹, _⟩ : Y) = y.1 at hy
          have h := congrArg Subtype.val hy
          simp only at h
          simp only [Finset.mem_filter]
          exact ⟨y.1.2, (commute_of_conj_eq h)⟩⟩
        invFun := fun w => ⟨⟨w.1, (Finset.mem_filter.mp w.2).1⟩, by
          change (⟨(u : G) * w.1 * (u : G)⁻¹, _⟩ : Y) = ⟨w.1, _⟩
          apply Subtype.ext
          simp only
          rw [← (Finset.mem_filter.mp w.2).2, mul_inv_cancel_right]⟩
        left_inv := fun y => rfl
        right_inv := fun w => rfl }
  have hTc : Fintype.card T = 4 := by
    rw [← Nat.card_eq_fintype_card]
    have := RootWeights.sylow_card_eq_two_part P hm hcard
    change Nat.card (P : Subgroup G) = 2 ^ 2 at this
    rw [this]
    norm_num
  let S4 : Finset T := {⟨1, one_mem _⟩, ⟨τ, hτP⟩, ⟨σ, hσP⟩, ⟨ρ, hρP⟩}
  have hS4 : S4.card = 4 := by
    simp only [S4]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h; exact hρσ (congrArg Subtype.val h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hτσ (congrArg Subtype.val h), fun h => hρτ (congrArg Subtype.val h).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hτ1 (congrArg Subtype.val h).symm, fun h => hσ1 (congrArg Subtype.val h).symm,
        fun h => hρ1 (congrArg Subtype.val h).symm⟩
  have hS4u : S4 = Finset.univ := Finset.eq_univ_of_card S4 (by rw [hS4, hTc])
  have hfilter1 : I'.filter (fun w => w * 1 = 1 * w) = I' := by
    ext w; simp
  have hfilterA (u : G) : I'.filter (fun w => w * u = u * w) = A u := rfl
  have hsum : ∑ u : T, Fintype.card (MulAction.fixedBy Y u) =
      I'.card + (A τ).card + (A σ).card + (A ρ).card := by
    rw [← hS4u]
    simp only [S4]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_pair]
    · rw [hfix, hfix, hfix, hfix]
      simp only
      rw [hfilter1, hfilterA, hfilterA, hfilterA]
      ring
    · intro h; exact hρσ (congrArg Subtype.val h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hτσ (congrArg Subtype.val h), fun h => hρτ (congrArg Subtype.val h).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hτ1 (congrArg Subtype.val h).symm, fun h => hσ1 (congrArg Subtype.val h).symm,
        fun h => hρ1 (congrArg Subtype.val h).symm⟩
  rw [hsum, hTc] at hB
  refine ⟨I'.card, (A τ).card, by omega, by omega, by omega, ?_⟩
  refine ⟨Fintype.card (Quotient (MulAction.orbitRel T Y)), ?_⟩
  omega

end
end C55FT
end

/-! ### Module `FTOnly.Eight` -/
section
/-! Sylow 2-subgroups of order eight.  An element of order four gives two
normalized cyclic subgroups, of orders two and four.  Unless one normalizer has
index five, their families already exceed the threshold; index five embeds the
group in the symmetric group on five letters. -/

namespace C55FT
open Conjecture55Lean4Web Conjecture55PartialCount Conjecture55ConjugateOdd
open Conjecture55ThreeFamilies Conjecture55Lean4Web.CyclicSum

/-- A family with normalizer index at least seven contributes at least
`7 / 2` times `2 ^ ω(m)`. -/
theorem seven_mul_le_family {m c n : ℕ} (hm : Odd m) (hmc : m = c * n) (ho : Odd n)
    (h7 : 7 ≤ n) : 7 * 2 ^ m.primeFactors.card ≤ 2 * (n * c.divisors.card) := by
  have e1 := seven_mul_two_pow_le_two_mul ho h7
  have e2 := two_pow_card_primeFactors_le_mul hmc hm.pos.ne'
  calc 7 * 2 ^ m.primeFactors.card
      ≤ 7 * (2 ^ n.primeFactors.card * c.divisors.card) := Nat.mul_le_mul_left 7 e2
    _ = (7 * 2 ^ n.primeFactors.card) * c.divisors.card := by ring
    _ ≤ (2 * n) * c.divisors.card := Nat.mul_le_mul_right _ e1
    _ = 2 * (n * c.divisors.card) := by ring

/-- When `m = 15`, a family with normalizer index at least five has at least ten
members. -/
theorem ten_le_family_fifteen {c n : ℕ} (hmc : 15 = c * n) (h5 : 5 ≤ n) :
    10 ≤ n * c.divisors.card := by
  have hn : n ∣ 15 := ⟨c, by rw [hmc, mul_comm]⟩
  have hn15 : n ≤ 15 := Nat.le_of_dvd (by norm_num) hn
  have hcases : (n = 5 ∧ c = 3) ∨ (n = 15 ∧ c = 1) := by
    interval_cases n <;> omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem five_or_fifteen {m : ℕ} (hm15 : m ∣ 15) (h5 : 5 ∣ m) : m = 5 ∨ m = 15 := by
  have hle := Nat.le_of_dvd (by norm_num) hm15
  interval_cases m <;> omega

theorem false_of_eight_two_part {G : Type} [Group G] [Fintype G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 3 * m) (P : Sylow 2 G)
    (hnc : ¬ IsCyclic P)
    (S : Subgroup G) [S.Normal] (hs : IsSimpleGroup S) (hn : ¬ IsMulCommutative S)
    (h4 : 4 ∣ Nat.card S) (hC : Subgroup.centralizer (S : Set G) = ⊥)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) : False := by
  classical
  obtain ⟨x, hx⟩ := RootWeights.exists_order_half_sylow_card_of_strict_fc_bound
    (le_refl 3) hm P hnc hcard (Conjecture55FrobeniusProof.rootCountLowerBound G) hlt
  have hx4 : orderOf x = 2 ^ 2 := by simpa using hx
  have hidx := zpowers_index_eq_two (by norm_num) hm hcard P x hx
  -- The subgroups of orders two and four.
  let Z : Subgroup G := Subgroup.zpowers ((x : G) ^ (2 ^ 1))
  let R : Subgroup G := Subgroup.zpowers ((x : G) ^ (2 ^ 0))
  have hZ : Nat.card Z = 2 ^ (0 + 1) := by
    rw [Nat.card_zpowers, orderOf_coe_pow_two_pow (P : Subgroup G) x hx4 (by norm_num)]
  have hR : Nat.card R = 2 ^ (1 + 1) := by
    rw [Nat.card_zpowers, orderOf_coe_pow_two_pow (P : Subgroup G) x hx4 (by norm_num)]
  have hZbot : Z ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hZ; norm_num at hZ
  have hRbot : R ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hR; norm_num at hR
  obtain ⟨cz, hcz, hmz, hoz, hlez⟩ := family_bound hm hcard P Z hZ
    (le_normalizer_zpowers_pow (P : Subgroup G) x hidx (2 ^ 1))
  obtain ⟨cr, hcr, hmr, hor, hler⟩ := family_bound hm hcard P R hR
    (le_normalizer_zpowers_pow (P : Subgroup G) x hidx (2 ^ 0))
  have h5z := normalizer_index_ge_five S hs hn h4 hC Z hZbot hoz
  have h5r := normalizer_index_ge_five S hs hn h4 hC R hRbot hor
  have hodd := divisors_card_le_cyclicDividing (G := G) (n := m)
    (by rw [hcard]; exact dvd_mul_left _ _)
  have hsum := cyclic_count_ge_odd_and_three_families (G := G) hm
  have hexp := threshold_eq (G := G) (by norm_num) hm hcard
  have hcyc : cyc G = Nat.card (CyclicSubgroups G) := rfl
  rw [hexp, hcyc] at hlt
  by_cases hbig : 7 ≤ (Subgroup.normalizer (Z : Set G)).index ∧
      7 ≤ (Subgroup.normalizer (R : Set G)).index
  · have fz := seven_mul_le_family hm hmz hoz hbig.1
    have fr := seven_mul_le_family hm hmr hor hbig.2
    have hτ := two_pow_card_primeFactors_le_card_divisors m hm.pos
    omega
  · -- One normalizer has index five, so the group embeds in S5.
    have hfive : (Subgroup.normalizer (Z : Set G)).index = 5 ∨
        (Subgroup.normalizer (R : Set G)).index = 5 := by
      have := Nat.odd_iff.mp hoz
      have := Nat.odd_iff.mp hor
      omega
    have h120 : Nat.card G ∣ 120 := by
      rcases hfive with h | h
      · have hd := card_dvd_factorial_index _ (normalCore_eq_bot_of_not_le S hs hC _
          (not_le_normalizer_of_cyclic S Z hs hn hC hZbot))
        rw [h] at hd
        simpa [Nat.factorial] using hd
      · have hd := card_dvd_factorial_index _ (normalCore_eq_bot_of_not_le S hs hC _
          (not_le_normalizer_of_cyclic S R hs hn hC hRbot))
        rw [h] at hd
        simpa [Nat.factorial] using hd
    have hm15 : m ∣ 15 := by
      rw [hcard] at h120
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2 ^ 3)
        (by simpa using h120)
    have h5m : 5 ∣ m := by
      rcases hfive with h | h
      · exact ⟨cz, by rw [hmz, h, mul_comm]⟩
      · exact ⟨cr, by rw [hmr, h, mul_comm]⟩
    rcases five_or_fifteen hm15 h5m with rfl | rfl
    · exact false_of_card_forty hrad (by rw [hcard]; norm_num)
    · have h17 := seventeen_le_cyclicDividing_fifteen hrad S hs hn hC
        (Or.inr (by rw [hcard]; norm_num))
      have kz := ten_le_family_fifteen hmz h5z
      have kr := ten_le_family_fifteen hmr h5r
      have hω : (15 : ℕ).primeFactors.card = 2 := by
        simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]
      rw [hω] at hlt
      omega

end C55FT
end

/-! ### Module `FTOnly.Four` -/
section
/-! The Klein four branch: `|G| = 4 m` with `m` odd.  The family of the
involution class exceeds the threshold unless there are few involutions; the
Sylow/involution combinatorics leave only fifteen involutions, which forces either
`3 ∣ m / 15` or `|G| = 60`.  In the latter case `1 + 15 + 10 + 6 = 32` cyclic
subgroups meet the threshold exactly. -/

namespace C55FT
open Conjecture55Lean4Web Subgroup Conjecture55PartialCount Conjecture55ConjugateOdd
open Conjecture55ThreeFamilies Conjecture55Lean4Web.CyclicSum

section
variable {G : Type} [Group G] [Fintype G]

/-- A normal subgroup of order divisible by four contains the Sylow subgroup. -/
theorem sylow_le_of_four_dvd {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m)
    (P : Sylow 2 G) (S : Subgroup G) [S.Normal] (h4 : 4 ∣ Nat.card S) :
    (P : Subgroup G) ≤ S := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSd : Nat.card S ∣ 2 ^ 2 * m := hcard ▸ Subgroup.card_subgroup_dvd_card S
  obtain ⟨s, hs⟩ := h4
  have hsm : s ∣ m := by
    rw [hs, show (2 : ℕ) ^ 2 = 4 by norm_num] at hSd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hSd
  have hso : Odd s := Odd.of_dvd_nat hm hsm
  have hSc : Nat.card S = 2 ^ 2 * s := by rw [hs]; norm_num
  let Q : Sylow 2 S := default
  have hQc : Nat.card Q = 2 ^ 2 := RootWeights.sylow_card_eq_two_part Q hso hSc
  let Qb : Subgroup G := (Q : Subgroup S).map S.subtype
  have hQbc : Nat.card Qb = 2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, ← Sylow.card_eq_multiplicity P,
      RootWeights.sylow_card_eq_two_part P hm hcard]
    exact hQc
  let Q' : Sylow 2 G := Sylow.ofCard Qb hQbc
  have hQ'S : (Q' : Subgroup G) ≤ S := by
    rw [Sylow.coe_ofCard]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G Q' P
  intro y hy
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  rw [MulAut.smul_def, MulAut.conj_apply]
  exact ‹S.Normal›.conj_mem q (hQ'S hq) x

/-- If the centralizer of `τ` has a unique Sylow 2-subgroup, it normalizes `P`. -/
theorem centralizer_le_normalizer_of_unique {m : ℕ} (hm : Odd m)
    (hcard : Nat.card G = 2 ^ 2 * m) (P : Sylow 2 G) (hnc : ¬ IsCyclic P) {τ : G}
    (hτP : τ ∈ (P : Subgroup G))
    (hj : Nat.card (Sylow 2 (centralizer ({τ} : Set G))) = 1) :
    centralizer ({τ} : Set G) ≤ normalizer ((P : Subgroup G) : Set G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer ({τ} : Set G)
  have hPC : (P : Subgroup G) ≤ C := le_centralizer_of_sylow_four hm hcard P hnc hτP
  obtain ⟨-, c, hc, -, hCc⟩ := factor_of_sylow_le hm hcard P C hPC
  let Q : Sylow 2 C := default
  have hQc : Nat.card Q = 2 ^ 2 := RootWeights.sylow_card_eq_two_part Q hc hCc
  have hT0c : Nat.card ((P : Subgroup G).subgroupOf C) = 2 ^ (Nat.card C).factorization 2 := by
    rw [← Sylow.card_eq_multiplicity Q, hQc, Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv,
      RootWeights.sylow_card_eq_two_part P hm hcard]
  let Q0 : Sylow 2 C := Sylow.ofCard _ hT0c
  let : Subsingleton (Sylow 2 C) := Finite.card_le_one_iff_subsingleton.mp hj.le
  have hQ0n : (Q0 : Subgroup C).Normal := Sylow.normal_of_subsingleton Q0
  rw [Sylow.coe_ofCard] at hQ0n
  have hfwd : ∀ x ∈ C, ∀ t ∈ (P : Subgroup G), x * t * x⁻¹ ∈ (P : Subgroup G) := by
    intro x hx t ht
    have h := hQ0n.conj_mem ⟨t, hPC ht⟩ (by simpa [mem_subgroupOf] using ht) ⟨x, hx⟩
    simpa [mem_subgroupOf] using h
  intro x hx
  rw [mem_normalizer_iff]
  intro t
  constructor
  · exact hfwd x hx t
  · intro ht
    have := hfwd x⁻¹ (inv_mem hx) _ ht
    simpa [mul_assoc] using this

/-- With a unique Sylow 2-subgroup in the centralizer of `τ`, the number of
involutions is at least fifteen, and fifteen embeds the group in `S₅`. -/
theorem index_ge_fifteen_of_unique [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m) (P : Sylow 2 G)
    (hnc : ¬ IsCyclic P) (S : Subgroup G) [S.Normal] (hs : IsSimpleGroup S)
    (hn : ¬ IsMulCommutative S) (h4 : 4 ∣ Nat.card S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥)
    {τ g : G} (hτP : τ ∈ (P : Subgroup G)) (hgN : g ∈ normalizer ((P : Subgroup G) : Set G))
    (hσ : g * τ * g⁻¹ ≠ τ)
    (hj : Nat.card (Sylow 2 (centralizer ({τ} : Set G))) = 1) :
    15 ≤ (centralizer ({τ} : Set G)).index ∧
      ((centralizer ({τ} : Set G)).index = 15 → Nat.card G ∣ 120) := by
  classical
  let T : Subgroup G := (P : Subgroup G)
  let C : Subgroup G := centralizer ({τ} : Set G)
  let N : Subgroup G := normalizer ((T : Subgroup G) : Set G)
  have hCN : C ≤ N := centralizer_le_normalizer_of_unique hm hcard P hnc hτP hj
  have hPC : T ≤ C := le_centralizer_of_sylow_four hm hcard P hnc hτP
  have hPN : T ≤ N := le_normalizer
  obtain ⟨-, c, hc, -, hCc⟩ := factor_of_sylow_le hm hcard P C hPC
  obtain ⟨hoN, a, ha, -, hNc⟩ := factor_of_sylow_le hm hcard P N hPN
  have hk := relIndex_mul_index hCN
  have hGC := C.card_mul_index
  have hGN := N.card_mul_index
  have hNpos : 0 < N.index := Nat.pos_of_ne_zero (index_ne_zero_of_finite)
  have hkeq : C.relIndex N * Nat.card C = Nat.card N := by
    apply Nat.eq_of_mul_eq_mul_right hNpos
    calc C.relIndex N * Nat.card C * N.index = Nat.card C * (C.relIndex N * N.index) := by ring
      _ = Nat.card C * C.index := by rw [hk]
      _ = Nat.card N * N.index := by rw [hGC, hGN]
  rw [hCc, hNc] at hkeq
  have hkc : C.relIndex N * c = a := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 2)
    rw [← hkeq]
    ring
  have hkodd : Odd (C.relIndex N) := Nat.Odd.of_mul_left (hkc ▸ ha)
  have hk1 : C.relIndex N ≠ 1 := by
    intro h1
    have hNC : N ≤ C := relIndex_eq_one.mp h1
    apply hσ
    have hgC : g ∈ C := hNC hgN
    have hcomm := mem_centralizer_singleton_iff.mp hgC
    rw [hcomm, mul_inv_cancel_right]
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x :=
    fun x hx y hy => mul_comm_of_mem_sylow hm hcard P hnc hx hy
  have hTc : Nat.card T = 4 := by
    have := RootWeights.sylow_card_eq_two_part P hm hcard
    change Nat.card T = 2 ^ 2 at this
    rw [this]; norm_num
  have hN1 : N.index ≠ 1 := by
    intro h1
    have hNtop : N = ⊤ := index_eq_one.mp h1
    have hTn : T.Normal := normalizer_eq_top_iff.mp hNtop
    have hTsol : Group.IsSolvable T :=
      Group.isSolvable_of_comm (fun x y => Subtype.ext (hTcomm x x.2 y y.2))
    have hbot := hrad T hTn hTsol
    rw [hbot, card_bot] at hTc
    norm_num at hTc
  have hSN : ¬ S ≤ N := by
    intro hSN
    have hTS : T ≤ S := sylow_le_of_four_dvd hm hcard P S h4
    have hnorm : (T.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hTS).mpr hSN
    rcases hs.eq_bot_or_eq_top_of_normal (T.subgroupOf S) with hb | ht
    · have hTbot : T = ⊥ := by
        rw [subgroupOf_eq_bot] at hb
        exact hb.eq_bot_of_le hTS
      rw [hTbot, card_bot] at hTc
      norm_num at hTc
    · have hST : S ≤ T := subgroupOf_eq_top.mp ht
      apply hn
      exact IsMulCommutative.of_comm fun x y => Subtype.ext (hTcomm x (hST x.2) y (hST y.2))
  have hcore := normalCore_eq_bot_of_not_le S hs hC N hSN
  have hGdvd := card_dvd_factorial_index N hcore
  have h4G : 4 ∣ Nat.card G := by rw [hcard]; exact ⟨m, by ring⟩
  have hN3 : N.index ≠ 3 := by
    intro h3
    rw [h3] at hGdvd
    have := h4G.trans hGdvd
    norm_num [Nat.factorial] at this
  have hNo := Nat.odd_iff.mp hoN
  have hko := Nat.odd_iff.mp hkodd
  refine ⟨?_, ?_⟩
  · rw [← hk]
    have hN5 : 5 ≤ N.index := by omega
    have hk3 : 3 ≤ C.relIndex N := by omega
    nlinarith
  · intro h15
    have hprod : C.relIndex N * N.index = 15 := by rw [hk]; exact h15
    have hN5 : N.index = 5 := by
      have hN5 : 5 ≤ N.index := by omega
      have hk3 : 3 ≤ C.relIndex N := by omega
      by_contra hne
      have : 6 ≤ N.index := by omega
      nlinarith
    rw [hN5] at hGdvd
    simpa [Nat.factorial] using hGdvd

/-- The Klein four branch of the minimal counterexample is impossible. -/
theorem false_of_four_two_part (hFT : OddOrderTheorem) [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ 2 * m) (P : Sylow 2 G)
    (hnc : ¬ IsCyclic P) (S : Subgroup G) [S.Normal] (hs : IsSimpleGroup S)
    (hn : ¬ IsMulCommutative S) (h4 : 4 ∣ Nat.card S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) : False := by
  classical
  obtain ⟨τ, g, hτP, hgN, hτ1, hσ, hρτ, hρσ⟩ := exists_conj_triple hFT hrad hm hcard P hnc
  have hτ2 : τ ^ 2 = 1 := sq_eq_one_of_mem_sylow hm hcard P hnc hτP
  have hconj : ∀ w : G, w ^ 2 = 1 → w ≠ 1 → ∃ x : G, x * τ * x⁻¹ = w :=
    fun w hw2 hw1 => exists_conj_of_involution hm hcard P hnc hτP hgN hτ1 hσ hρτ hρσ hw2 hw1
  have hi := card_invFinset_eq_index hτ2 hτ1 hconj
  let A : Subgroup G := zpowers τ
  have hτo : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ1
  have hA : Nat.card A = 2 ^ (0 + 1) := by rw [Nat.card_zpowers, hτo]; norm_num
  have hNA := normalizer_zpowers_eq_centralizer hτ2 hτ1
  have hPN : (P : Subgroup G) ≤ normalizer (A : Set G) := by
    rw [hNA]
    exact le_centralizer_of_sylow_four hm hcard P hnc hτP
  obtain ⟨c, hc, hmc, ho, hle0⟩ := family_bound hm hcard P A hA hPN
  have hAbot : A ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hA
    norm_num at hA
  have h5 := normalizer_index_ge_five S hs hn h4 hC A hAbot ho
  have hodd := divisors_card_le_cyclicDividing (G := G) (n := m)
    (by rw [hcard]; exact dvd_mul_left _ _)
  have hsum := cyclic_count_ge_odd_and_three_families (G := G) hm
  have hexp := threshold_eq (G := G) (by norm_num) hm hcard
  have hcyc : cyc G = Nat.card (CyclicSubgroups G) := rfl
  rw [hexp, hcyc] at hlt
  have hτm := two_pow_card_primeFactors_le_card_divisors m hm.pos
  set n := (normalizer (A : Set G)).index with hndef
  by_cases h7 : 7 * 2 ^ n.primeFactors.card ≤ n
  · have e2 := two_pow_card_primeFactors_le_mul hmc hm.pos.ne'
    have key : 7 * 2 ^ m.primeFactors.card ≤ n * c.divisors.card := by
      calc 7 * 2 ^ m.primeFactors.card
          ≤ 7 * (2 ^ n.primeFactors.card * c.divisors.card) := Nat.mul_le_mul_left 7 e2
        _ = (7 * 2 ^ n.primeFactors.card) * c.divisors.card := by ring
        _ ≤ n * c.divisors.card := Nat.mul_le_mul_right _ h7
    omega
  · have hE := mem_small_of_lt_seven_mul ho h5 (by omega)
    obtain ⟨a, b, hia, hfb, hab, h4ab⟩ :=
      involution_constraints hm hcard P hnc hτP hgN hτ1 hσ hρτ hρσ
    have hf := card_commute_eq_one_add_two_mul hm hcard P hnc hτP hτ1
    set j := Nat.card (Sylow 2 (centralizer ({τ} : Set G))) with hjdef
    have hjodd : j % 2 = 1 := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact card_sylow_modEq_one 2 (centralizer ({τ} : Set G))
    have hni : n = a + 3 := by rw [hndef, hNA, ← hi, hia]
    have hfj : b + 3 = 1 + 2 * j := by rw [← hfb, hf]
    by_cases hj1 : j = 1
    · obtain ⟨hge, h120⟩ :=
        index_ge_fifteen_of_unique hrad hm hcard P hnc S hs hn h4 hC hτP hgN hσ hj1
      rw [← hNA, ← hndef] at hge h120
      have hn15 : n = 15 := by
        rcases hE with h | h | h | h | h | h | h <;> omega
      have hG := h120 hn15
      rw [hn15] at hmc
      have hm30 : m ∣ 30 := by
        rw [hcard] at hG
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2 ^ 2) (by simpa using hG)
      have hmle := Nat.le_of_dvd (by norm_num) hm30
      have hco := Nat.odd_iff.mp hc
      have hc1 : c = 1 := by omega
      have hm15 : m = 15 := by omega
      have hG60 : Nat.card G = 60 := by rw [hcard, hm15]; norm_num
      have h17 := seventeen_le_cyclicDividing_fifteen hrad S hs hn hC (Or.inl hG60)
      have hω : (15 : ℕ).primeFactors.card = 2 := by
        simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]
      rw [hm15, hω] at hlt
      rw [hm15] at hsum
      rw [hn15, hc1, Nat.divisors_one, Finset.card_singleton, mul_one] at hle0
      omega
    · have hcase : n = 15 ∧ j = 3 := by
        rcases hE with h | h | h | h | h | h | h <;> omega
      obtain ⟨hn15, hj3⟩ := hcase
      obtain ⟨-, c', hc', hmc', hNc'⟩ :=
        factor_of_sylow_le hm hcard P (normalizer (A : Set G)) hPN
      have hcc : c' = c := by
        rw [← hndef] at hmc'
        rw [hmc'] at hmc
        exact Nat.eq_of_mul_eq_mul_right (show 0 < n by omega) hmc
      have hjdvd : j ∣ Nat.card (centralizer ({τ} : Set G)) := by
        let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        let Q : Sylow 2 (centralizer ({τ} : Set G)) := default
        exact (Sylow.card_dvd_index Q).trans (Subgroup.index_dvd_card _)
      rw [hj3, ← hNA, hNc', hcc] at hjdvd
      have h3c : 3 ∣ c := by
        norm_num at hjdvd
        omega
      have hωm : m.primeFactors.card ≤ c.primeFactors.card + 1 := by
        rw [hmc, hn15, Nat.primeFactors_mul hc.pos.ne' (by norm_num)]
        have h15 : (15 : ℕ).primeFactors = {3, 5} := by
          simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]
        rw [h15]
        have h3m : 3 ∈ c.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3c, hc.pos.ne'⟩
        calc (c.primeFactors ∪ {3, 5}).card ≤ (insert 5 c.primeFactors).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
              rcases hx with h | h | h
              · exact Or.inr h
              · exact Or.inr (h ▸ h3m)
              · exact Or.inl h
          _ ≤ c.primeFactors.card + 1 := Finset.card_insert_le _ _
      have hτc := two_pow_card_primeFactors_le_card_divisors c hc.pos
      have hτcm : c.divisors.card ≤ m.divisors.card :=
        Finset.card_le_card (Nat.divisors_subset_of_dvd hm.pos.ne' ⟨n, hmc⟩)
      have h2 : 2 ^ m.primeFactors.card ≤ 2 * 2 ^ c.primeFactors.card := by
        calc 2 ^ m.primeFactors.card ≤ 2 ^ (c.primeFactors.card + 1) :=
              Nat.pow_le_pow_right (by norm_num) hωm
          _ = 2 * 2 ^ c.primeFactors.card := by ring
      rw [hn15] at hle0
      omega

end
end C55FT
end

/-! ### Module `OddOrder.Isaacs.Ch09_MoreSubnormality.Quasisimple` -/
section
/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# Isaacs Ch. 9 — §9A: quasisimple groups (pp. 271-273)

Isaacs, *Finite Group Theory* (AMS GSM 92), Ch. 9 "More on Subnormality" 冒頭.
Bender の generalized Fitting subgroup `F*(G)` に向けた quasisimple 群の基礎:

- `IsQuasisimple`: `G` が **quasisimple** ⟺ `G` が perfect かつ `G/Z(G)` が simple
  (書籍 p. 272 の定義そのまま; `G/Z(G)` は自動的に nonabelian simple になる).
- **Lemma 9.1** (`not_isMulCommutative_of_isSimpleGroup_quotient_center`,
  `isQuasisimple_commutator`, `commutatorQuotientCenterEquiv`): `G/Z(G)` が simple なら
  `G/Z(G)` は nonabelian, `G'` は perfect (よって quasisimple), かつ `G'/Z(G') ≅ G/Z(G)`.
- **Lemma 9.2** (`IsQuasisimple.normal_le_center` / `IsQuasisimple.quotient`):
  quasisimple `G` の proper normal subgroup は central, nonidentity 商は quasisimple.

有限性は仮定しない (Isaacs は有限群の本だが §9A のこの部分は一般に成立する).
component / layer / `F*(G)` は後続 leaf (`Components.lean` 以降) で扱う.

## 実装ノート

書籍の Lemma 9.1 は `G'''` の非自明性経由で `G'' = G'` を出すが、ここでは商
`G/Z(G)` 側で完結する短い route を採る: `Z := Z(G)` への射影 `π` で
`π(G') = commutator (G/Z) = ⊤` (simple nonabelian なので全体), よって
`π(⁅G',G'⁆) = ⁅⊤,⊤⁆ = ⊤`, すなわち `⁅G',G'⁆ ⊔ Z = ⊤`. 一般補題
`commutator_le_of_sup_center_eq_top` (「normal `N` が `N ⊔ Z(G) = ⊤` を満たせば
`G' ≤ N`」= 「中心的補部分をもつ商は可換」) を `N := ⁅G',G'⁆` に適用して
`G' ≤ ⁅G',G'⁆` を得る. 同じ一般補題が Lemma 9.2(a) も処理する.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type*} [Group G]

section /- 9A 補助: 可換性と commutator の一般補題 -/

/-- 可換群からの全射があれば値域も可換. -/
theorem isMulCommutative_of_surjective {H : Type*} [Group H] [IsMulCommutative G]
    (f : G →* H) (hf : Function.Surjective f) : IsMulCommutative H :=
  IsMulCommutative.of_comm fun x y => by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, mul_comm' a b]

end

section /- 9A: Lemma 9.1 (p. 272) -/

end

section /- 9A: Lemma 9.2 (p. 272) と quasisimple の基本 API -/

end

end OddOrder.Isaacs.Ch09
end

/-! ### Module `OddOrder.Mathlib.Subgroup` -/
section
/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# Auxiliary `Subgroup` lemmas

mathlib v4.29.1 に不在の汎用 `Subgroup` 補題. 主に
[`OddOrder/GroupTheory/ChermakDelgado.lean`](../GroupTheory/ChermakDelgado.lean) の
支援目的だが, 他章でも独立に使う可能性があるため `OddOrder.Mathlib` 配下に切り出す
("mathlib upstream 候補" の慣用 dir).

## Main results

* `Subgroup.card_HK_mul_card_inf_eq_card_mul_card`: 古典的
  `|HK| · |H ∩ K| = |H| · |K|` (集合積 `HK ⊆ G` は一般に部分群ではない).
* `Subgroup.le_centralizer_centralizer`: `H ≤ C_G(C_G(H))`
  (`IsMulCommutative` 仮定なし; 既存 `Subgroup.le_centralizer` は仮定あり版).
* `Subgroup.centralizer_centralizer_centralizer`: Galois closure idempotency
  `C_G(C_G(C_G(H))) = C_G(H)`.
* `Subgroup.centralizer_sup`: `C_G(H ⊔ K) = C_G(H) ⊓ C_G(K)`
  (mathlib には Subalgebra 版のみ).
* `Subgroup.card_quotient_lt_of_ne_bot`: a finite quotient by a nontrivial subgroup
  has strictly smaller cardinality.

将来 mathlib 本体へ寄与する際の配置候補:

* `card_HK_mul_card_inf_eq_card_mul_card` → `Mathlib/GroupTheory/Coset/Card.lean`
* `le_centralizer_centralizer`, `centralizer_centralizer_centralizer`,
  `centralizer_sup` → `Mathlib/GroupTheory/Subgroup/Centralizer.lean`
-/

namespace Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise

/-- **Classical identity**: `|HK| · |H ∩ K| = |H| · |K|` for subgroups `H, K` of a
group `G`, where `HK ⊆ G` is the set product (not generally a subgroup).
無限群でも両辺はゼロで成立する.

mathlib v4.29.1 不在 ── 関連 `index_inf_le`, `relIndex_inf_mul_relIndex` は部分対応のみ.

**証明戦略**: `H × K → HK` の準同型 (の corestriction) は H ⊓ K 加群作用で fiber が
`|H ∩ K|` と分かる. mathlib 流には:
1. `card_mul_eq_card_subgroup_mul_card_quotient` で `|HK| = |K| · |(↑H).image mk|`.
2. `H ⧸ K.subgroupOf H ≃ (↑H).image mk` (本証明内で構成).
3. Lagrange `|H| = |H ⧸ K.subgroupOf H| · |K.subgroupOf H|`.
4. `K.subgroupOf H = (H ⊓ K).subgroupOf H`, `subgroupOfEquivOfLe` で `≃ H ⊓ K`. -/
theorem card_HK_mul_card_inf_eq_card_mul_card (H K : Subgroup G) :
    Nat.card (↑H * ↑K : Set G) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  classical
  -- Step 1: `|HK| = |K| · |(↑H).image mk|` (mathlib 既存)
  rw [card_mul_eq_card_subgroup_mul_card_quotient K (↑H : Set G)]
  -- Step 2: 補助 — corestricted projection `f : H → img` は全射
  set img := (↑H : Set G).image (QuotientGroup.mk : G → G ⧸ K) with himg
  let f : H → ↥img := fun h => ⟨QuotientGroup.mk h.val, h.val, h.property, rfl⟩
  have hf_surj : Function.Surjective f := by
    rintro ⟨_, h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  -- Step 3: Setoid.ker f は QuotientGroup.leftRel (K.subgroupOf H) と関係が一致
  have hsetoid_rel :
      ∀ h₁ h₂ : H,
        (QuotientGroup.leftRel (K.subgroupOf H)) h₁ h₂ ↔ (Setoid.ker f) h₁ h₂ := by
    intro h₁ h₂
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf, Setoid.ker_def]
    constructor
    · intro hrel
      apply Subtype.ext
      change QuotientGroup.mk h₁.val = QuotientGroup.mk h₂.val
      rw [QuotientGroup.eq]
      exact hrel
    · intro hrel
      have : QuotientGroup.mk h₁.val = (QuotientGroup.mk h₂.val : G ⧸ K) :=
        congrArg Subtype.val hrel
      rwa [QuotientGroup.eq] at this
  -- Step 4: H ⧸ K.subgroupOf H ≃ ↥img (合成)
  have hquot_img_card : Nat.card (H ⧸ K.subgroupOf H) = Nat.card ↥img :=
    (Nat.card_congr (Quotient.congrRight hsetoid_rel)).trans
      (Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf_surj))
  -- Step 5: Lagrange in H
  have hH_split : Nat.card H = Nat.card (H ⧸ K.subgroupOf H) * Nat.card ↥(K.subgroupOf H) :=
    (K.subgroupOf H).card_eq_card_quotient_mul_card_subgroup
  -- Step 6: `K.subgroupOf H = (H ⊓ K).subgroupOf H`, `subgroupOfEquivOfLe` で
  -- `|K.subgroupOf H| = |H ⊓ K|`
  have hKHinf : K.subgroupOf H = (H ⊓ K).subgroupOf H := by
    ext x
    simp only [mem_subgroupOf, mem_inf, and_iff_right x.property]
  have hker_card : Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [hKHinf]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : H ⊓ K ≤ H)).toEquiv
  -- Step 7: 合算
  rw [hquot_img_card, hker_card] at hH_split
  -- hH_split : Nat.card H = Nat.card ↥img * Nat.card ↥(H ⊓ K)
  -- Goal: Nat.card K * Nat.card ↥img * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K
  rw [mul_assoc, ← hH_split, Nat.mul_comm]

/-- `H ≤ C_G(C_G(H))` for any subgroup `H` ── classical Galois connection (`le_centralizer_iff`).

mathlib v4.29.1 不在: 既存 `Subgroup.le_centralizer` は `IsMulCommutative H` 仮定が必要だが,
本補題は仮定なし. `Subgroup.closure_le_centralizer_centralizer` を `H = closure ↑H` に適用. -/
theorem le_centralizer_centralizer (H : Subgroup G) :
    H ≤ centralizer (centralizer (H : Set G) : Set G) := by
  conv_lhs => rw [← H.closure_eq]
  exact closure_le_centralizer_centralizer _

/-- `C_G(H ⊔ K) = C_G(H) ⊓ C_G(K)`.

mathlib v4.29.1 では `Subalgebra` 版 (`Algebra/Subalgebra/Centralizer.lean:19`) のみで,
`Subgroup` 版は不在. `Set.centralizer_union` + `Subgroup.centralizer_closure` から従う. -/
theorem centralizer_sup (H K : Subgroup G) :
    centralizer ((H ⊔ K : Subgroup G) : Set G)
      = centralizer (H : Set G) ⊓ centralizer (K : Set G) := by
  have hHK : (H ⊔ K : Subgroup G) = closure ((H : Set G) ∪ (K : Set G)) := by
    rw [closure_union, closure_eq, closure_eq]
  rw [hHK, centralizer_closure]
  ext g
  simp only [mem_centralizer_iff, Set.mem_union, mem_inf, or_imp, forall_and]

/-- **`MulAut` 作用の部分群 `J` の各点固定化群** (作用する側 `A` の中で取る): `φ a` が `J` を
元ごとに固定するような `a ∈ A` 全体.  `fixedPointsOfMulAut` (固定される側 `G` の中で取る) の双対.

下流: Peterfalvi (9.7)(a) — ブロック `H_i` の各点固定化群が `C_U(H_i)`, その指数が書籍の `a`
(issue 0152). -/
def ptStabOfMulAut {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) (J : Subgroup G) :
    Subgroup A where
  carrier := {a | ∀ x ∈ J, (φ a) x = x}
  one_mem' := fun x _ => by rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb x hx => by
    rw [map_mul]
    change (φ a) ((φ b) x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    rw [map_inv]
    change (φ a).symm x = x
    exact (MulEquiv.symm_apply_eq _).mpr (ha x hx).symm

@[simp]
theorem mem_ptStabOfMulAut {A G : Type*} [Group A] [Group G]
    {φ : A →* MulAut G} {J : Subgroup G} {a : A} :
    a ∈ ptStabOfMulAut φ J ↔ ∀ x ∈ J, (φ a) x = x := Iff.rfl

/-- **`MulAut` 作用の固定点部分群**: `φ : A →* MulAut G` の下で `∀ a, (φ a) g = g` を
満たす要素全体. mathlib `MulAction.fixedPoints` は Set だが, MulAut 作用の場合は
group 構造を持つので Subgroup として bundle.

下流: Isaacs Lem 4.32 後半 (P p-group on G p-group ⇒ fixedPoints > 1) で使用. -/
def fixedPointsOfMulAut {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    Subgroup G where
  carrier := {g | ∀ a : A, (φ a) g = g}
  one_mem' := fun a => map_one (φ a)
  mul_mem' := fun {x y} hx hy a => by rw [map_mul, hx, hy]
  inv_mem' := fun {x} hx a => by rw [map_inv, hx]

@[simp]
theorem mem_fixedPointsOfMulAut {A G : Type*} [Group A] [Group G]
    {φ : A →* MulAut G} {g : G} :
    g ∈ fixedPointsOfMulAut φ ↔ ∀ a : A, (φ a) g = g := Iff.rfl

/-- 自明作用 (`1 : A →* MulAut G`) の固定点は `⊤` (全要素が固定). -/
@[simp]
theorem fixedPointsOfMulAut_one_eq_top {A G : Type*} [Group A] [Group G] :
    fixedPointsOfMulAut (1 : A →* MulAut G) = ⊤ := by
  ext g
  simp only [mem_fixedPointsOfMulAut, Subgroup.mem_top, iff_true]
  intro a
  rfl

/-- **`p`-th power subgroup is characteristic** in CommGroup: for any `n : ℕ`, the range
of `powMonoidHom n` (= `{x^n : x : M}` as subgroup of M) is characteristic in M.

mathlib v4.29.1 不在の generic lemma. Lucchini K=⊥ (M abelian case で `φ(M) ⊴ G` を
`characteristic in normal` 経由で得る) で使用. -/
instance powMonoidHom_range_characteristic
    {M : Type*} [CommGroup M] (n : ℕ) :
    ((powMonoidHom (α := M) n).range).Characteristic := by
  refine ⟨fun φ => ?_⟩
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hφx
    obtain ⟨y, hy⟩ := hφx
    refine ⟨φ.symm y, ?_⟩
    have : φ ((φ.symm y) ^ n) = φ x := by
      rw [map_pow, MulEquiv.apply_symm_apply]
      exact hy
    exact φ.injective this
  · intro hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨φ y, ?_⟩
    change (φ y) ^ n = φ x
    rw [← map_pow]
    exact congrArg φ hy

end Subgroup

/-! ### `AddSubgroup.closure` and `Submodule.span` over `ZMod n`

In a `ZMod n`-module the order isomorphism `AddSubgroup.toZModSubmodule` carries subgroups to
submodules without changing the underlying set, so it also carries the subgroup generated by a
set to the submodule spanned by it.  This is the bridge used when a spanning hypothesis is stated
as a *subgroup* closure but the arithmetic input (a rank computation over `ZMod n`) is a *span*
— e.g. for the relation lattice of BG Appendix C, Problem 1 (issue 0180). -/

end

/-! ### Module `OddOrder.GroupTheory.ChermakDelgado` -/
section
/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# Chermak-Delgado measure, lattice, and subgroup

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), §1G (pp. 41-44, Theorems 1.41-1.46) の Lean 化.

mathlib upstream 候補として `OddOrder/GroupTheory/` 配下に shared module 化 (`IsElementaryAbelian`,
`Subgroup.thompsonJ` 系の慣用).

## Main definitions

* `Subgroup.chermakDelgadoMeasure H` (`m_G(H)`): `|H| · |C_G(H)|`.
* `Subgroup.chermakDelgadoLattice G` (`L(G)`): the set of subgroups attaining the maximum measure.
* `Subgroup.chermakDelgadoSubgroup G` (`M`): the minimal element of `L(G)` (= ⨅ L).

## Main results (this file: Lemmas 1.42, 1.43)

* `chermakDelgadoMeasure_le_centralizer` (Lemma 1.42): `m_G(H) ≤ m_G(C_G(H))`.
* `chermakDelgadoMeasure_mul_le` (Lemma 1.43): `m_G(H) · m_G(K) ≤ m_G(D) · m_G(J)`
  for `D = H ⊓ K`, `J = H ⊔ K`.

Thm 1.44 / Cor 1.45 / Thm 1.41 / Cor 1.46 は同ファイル後半.

## References

* Isaacs, M.: *Finite Group Theory* (AMS GSM 92, 2008), §1G, pp. 41-44.
* mathlib 不在の補助補題は [`OddOrder.Mathlib.Subgroup`](../Mathlib/Subgroup.lean):
  H1 (`card_HK_mul_card_inf_eq_card_mul_card`), H2 (`le_centralizer_centralizer`),
  `centralizer_sup` を使用.
-/

namespace Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise

/-- **Chermak-Delgado measure** of a subgroup: `m_G(H) := |H| · |C_G(H)|`.

Isaacs §1G p.41 の定義. 無限群でも well-defined だが (`Nat.card` が 0 を返す),
実質的に意味があるのは [Finite G] 下. -/
noncomputable def chermakDelgadoMeasure (H : Subgroup G) : ℕ :=
  Nat.card H * Nat.card (centralizer (H : Set G) : Subgroup G)

@[simp]
theorem chermakDelgadoMeasure_def (H : Subgroup G) :
    H.chermakDelgadoMeasure = Nat.card H * Nat.card (centralizer (H : Set G) : Subgroup G) :=
  rfl

/-- **Chermak-Delgado lattice** `L(G)`: the collection of subgroups attaining the maximum
Chermak-Delgado measure. Isaacs §1G p.42 (Thm 1.44 statement). -/
def chermakDelgadoLattice (G : Type*) [Group G] : Set (Subgroup G) :=
  {H | ∀ K : Subgroup G, K.chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure}

/-- **Chermak-Delgado subgroup** `M`: the minimal element of the maximum-measure lattice.
Isaacs Cor 1.45 で唯一の極小元として定義される (本ファイルで Cor 1.45 として証明). -/
noncomputable def chermakDelgadoSubgroup (G : Type*) [Group G] : Subgroup G :=
  ⨅ H ∈ chermakDelgadoLattice G, H

/-- **Isaacs Lemma 1.42**: `m_G(H) ≤ m_G(C_G(H))`.
等号成立は `H = C_G(C_G(H))` のとき (本ファイル `..._eq_iff` 系で別途扱う).

証明: `H ≤ C_G(C_G(H))` (`le_centralizer_centralizer`, mathlib 拡張) から
`|H| ≤ |C_G(C_G(H))|`, 両辺に `|C_G(H)|` を掛けて結論. -/
theorem chermakDelgadoMeasure_le_centralizer [Finite G] (H : Subgroup G) :
    H.chermakDelgadoMeasure
      ≤ (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
  -- Goal: |H| * |C_H| ≤ |C_H| * |C_(C_H)|
  rw [Nat.mul_comm (Nat.card ↥(centralizer (H : Set G)))]
  -- Goal: |H| * |C_H| ≤ |C_(C_H)| * |C_H|
  exact Nat.mul_le_mul_right _
    (Nat.card_le_card_of_injective (Subgroup.inclusion H.le_centralizer_centralizer)
      (Subgroup.inclusion_injective _))

/-- **Isaacs Lemma 1.43**: `m_G(H) · m_G(K) ≤ m_G(D) · m_G(J)` for `D = H ⊓ K`, `J = H ⊔ K`.

証明戦略 (Isaacs p.42):
- `|H|·|K| = |HK|·|D|` (H1).
- `|C_H|·|C_K| = |C_H·C_K|·|C_H ∩ C_K| = |C_H·C_K|·|C_J|` (H1 + `centralizer_sup`).
- `HK ⊆ J` ⟹ `|HK| ≤ |J|`.
- `C_H·C_K ⊆ C_D` ⟹ `|C_H·C_K| ≤ |C_D|`.
- 組合せて `|HK|·|C_H·C_K| ≤ |J|·|C_D|`, 両辺に `|D|·|C_J|` を掛けて結論. -/
theorem chermakDelgadoMeasure_mul_le [Finite G] (H K : Subgroup G) :
    H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      ≤ (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure := by
  set D := H ⊓ K with hD_def
  set J := H ⊔ K with hJ_def
  set C_H : Subgroup G := centralizer (H : Set G) with hCH_def
  set C_K : Subgroup G := centralizer (K : Set G) with hCK_def
  set C_D : Subgroup G := centralizer (D : Set G) with hCD_def
  set C_J : Subgroup G := centralizer (J : Set G) with hCJ_def
  -- 核心等式: C_J = C_H ⊓ C_K
  have hCJ_inf : C_J = C_H ⊓ C_K := centralizer_sup H K
  -- H1 for H, K
  have h1_HK : Nat.card (↑H * ↑K : Set G) * Nat.card ↥D = Nat.card H * Nat.card K :=
    card_HK_mul_card_inf_eq_card_mul_card H K
  -- H1 for C_H, C_K
  have h1_CHCK :
      Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card ↥(C_H ⊓ C_K)
        = Nat.card C_H * Nat.card C_K :=
    card_HK_mul_card_inf_eq_card_mul_card C_H C_K
  rw [← hCJ_inf] at h1_CHCK
  -- HK ⊆ J (集合包含)
  have hHK_sub_J : (↑H * ↑K : Set G) ⊆ (J : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)
  -- C_H * C_K ⊆ C_D (集合包含); C_H ⊆ C_D, C_K ⊆ C_D ⟹ 積も ⊆
  have hC_sub_CD : (C_H : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_left : D ≤ H)))
  have hCK_sub_CD : (C_K : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_right : D ≤ K)))
  have hCHCK_sub_CD : ((C_H : Set G) * (C_K : Set G) : Set G) ⊆ (C_D : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (hC_sub_CD hh) (hCK_sub_CD hk)
  -- cardinality monotonicity (with [Finite G])
  have hHK_le_J : Nat.card (↑H * ↑K : Set G) ≤ Nat.card J :=
    Nat.card_mono (Set.toFinite _) hHK_sub_J
  have hCHCK_le_CD : Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) ≤ Nat.card C_D :=
    Nat.card_mono (Set.toFinite _) hCHCK_sub_CD
  have main_ineq :
      Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G)
        ≤ Nat.card J * Nat.card C_D :=
    Nat.mul_le_mul hHK_le_J hCHCK_le_CD
  -- 仕上げ: 代数的整理
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def, chermakDelgadoMeasure_def,
      chermakDelgadoMeasure_def]
  calc Nat.card H * Nat.card C_H * (Nat.card K * Nat.card C_K)
      = (Nat.card H * Nat.card K) * (Nat.card C_H * Nat.card C_K) := by ring
    _ = (Nat.card (↑H * ↑K : Set G) * Nat.card ↥D)
          * (Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card C_J) := by
          rw [h1_HK, h1_CHCK]
    _ = (Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G))
          * (Nat.card ↥D * Nat.card C_J) := by ring
    _ ≤ (Nat.card J * Nat.card C_D) * (Nat.card ↥D * Nat.card C_J) :=
          Nat.mul_le_mul_right _ main_ineq
    _ = Nat.card ↥D * Nat.card C_D * (Nat.card J * Nat.card C_J) := by ring

/-! ### Thm 1.44 (a)(b)(c): `L(G)` is a lattice; structure properties.

主要 helper: Lemma 1.43 の等式条件 `m_G(H) * m_G(K) = m_G(D) * m_G(J)` から
`|HK| = |J|` と `|C_H * C_K| = |C_D|` を導出する. `H, K ∈ L` のとき equality を取る. -/

/-- 数論的補助: `a * b = c * d`, `a ≤ c`, `b ≤ d`, `c, b > 0` のとき `a = c ∧ b = d`. -/
private lemma _eq_of_mul_eq_of_le {a b c d : ℕ} (h_eq : a * b = c * d)
    (ha : a ≤ c) (hb : b ≤ d) (hc : 0 < c) (hb_pos : 0 < b) :
    a = c ∧ b = d := by
  have h1 : a * b ≤ c * b := Nat.mul_le_mul_right b ha
  have h2 : c * b ≤ c * d := Nat.mul_le_mul_left c hb
  have h_cb : a * b = c * b := le_antisymm h1 (h_eq ▸ h2)
  have ha_eq : a = c := Nat.eq_of_mul_eq_mul_right hb_pos h_cb
  subst ha_eq
  have hb_eq : b = d := Nat.eq_of_mul_eq_mul_left hc h_eq
  exact ⟨rfl, hb_eq⟩

/-- 数論的補助 (対称): `a * b = m * m`, `a ≤ m`, `b ≤ m` のとき `a = m ∧ b = m`. -/
private lemma _eq_of_mul_eq_sq_of_le {a b m : ℕ} (h_eq : a * b = m * m)
    (ha : a ≤ m) (hb : b ≤ m) : a = m ∧ b = m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact ⟨Nat.le_zero.mp ha, Nat.le_zero.mp hb⟩
  · rcases Nat.eq_zero_or_pos b with hb_z | hb_pos
    · subst hb_z
      rw [Nat.mul_zero] at h_eq
      have : m = 0 := by
        rcases Nat.mul_eq_zero.mp h_eq.symm with h | h <;> exact h
      omega
    · exact _eq_of_mul_eq_of_le h_eq ha hb hm hb_pos

/-- **Isaacs Lemma 1.43 (等号条件)** (p. 41): `m_G(H)·m_G(K) = m_G(D)·m_G(J)`
(`D = H ⊓ K`, `J = H ⊔ K`) が成り立つならば **`J = HK` かつ `C_G(D) = C_G(H)·C_G(K)`**
(いずれも集合としての等式).

書籍の証明そのまま. 不等式 `chermakDelgadoMeasure_mul_le` の導出では
`|HK| ≤ |J|` と `|C_H·C_K| ≤ |C_D|` の 2 箇所でしか緩みが生じないので, 等号成立時は
両方が等号になる. あとは有限集合の包含 + 濃度一致から集合等式が出る.

(配置: 書籍では主不等式 `chermakDelgadoMeasure_mul_le` の直後だが, 証明が下の私的補助
`_eq_of_mul_eq_of_le` を使うのでここに置く.) -/
theorem chermakDelgadoMeasure_mul_eq_conditions [Finite G] (H K : Subgroup G)
    (heq : H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      = (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure) :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) ∧
      ((centralizer ((H ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G)
        = (centralizer (H : Set G) : Set G) * (centralizer (K : Set G) : Set G) := by
  set D := H ⊓ K with hD_def
  set J := H ⊔ K with hJ_def
  set C_H : Subgroup G := centralizer (H : Set G) with hCH_def
  set C_K : Subgroup G := centralizer (K : Set G) with hCK_def
  set C_D : Subgroup G := centralizer (D : Set G) with hCD_def
  set C_J : Subgroup G := centralizer (J : Set G) with hCJ_def
  -- 主不等式の証明と同じ H1 分解.
  have hCJ_inf : C_J = C_H ⊓ C_K := centralizer_sup H K
  have h1_HK : Nat.card (↑H * ↑K : Set G) * Nat.card ↥D = Nat.card H * Nat.card K :=
    card_HK_mul_card_inf_eq_card_mul_card H K
  have h1_CHCK :
      Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card ↥(C_H ⊓ C_K)
        = Nat.card C_H * Nat.card C_K :=
    card_HK_mul_card_inf_eq_card_mul_card C_H C_K
  rw [← hCJ_inf] at h1_CHCK
  have h_LHS_decomp : H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      = (Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G))
        * (Nat.card ↥D * Nat.card C_J) := by
    rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
    calc Nat.card H * Nat.card C_H * (Nat.card K * Nat.card C_K)
        = (Nat.card H * Nat.card K) * (Nat.card C_H * Nat.card C_K) := by ring
      _ = (Nat.card (↑H * ↑K : Set G) * Nat.card ↥D)
            * (Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card C_J) := by
            rw [h1_HK, h1_CHCK]
      _ = _ := by ring
  have h_RHS_decomp : D.chermakDelgadoMeasure * J.chermakDelgadoMeasure
      = (Nat.card J * Nat.card C_D) * (Nat.card ↥D * Nat.card C_J) := by
    rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
    ring
  rw [h_LHS_decomp, h_RHS_decomp] at heq
  -- `|D|·|C_J| > 0` で両辺からキャンセル.
  have hDCJ_pos : 0 < Nat.card ↥D * Nat.card C_J := Nat.mul_pos Nat.card_pos Nat.card_pos
  have h_cancelled :
      Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G)
        = Nat.card J * Nat.card C_D :=
    Nat.eq_of_mul_eq_mul_right hDCJ_pos heq
  -- 2 本の包含と, それぞれの濃度不等式.
  have hHK_sub_J : (↑H * ↑K : Set G) ⊆ (J : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)
  have hC_sub_CD : (C_H : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_left : D ≤ H)))
  have hCK_sub_CD : (C_K : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_right : D ≤ K)))
  have hCHCK_sub_CD : ((C_H : Set G) * (C_K : Set G) : Set G) ⊆ (C_D : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (hC_sub_CD hh) (hCK_sub_CD hk)
  have hHK_le_J : Nat.card (↑H * ↑K : Set G) ≤ Nat.card J :=
    Nat.card_mono (Set.toFinite _) hHK_sub_J
  have hCHCK_le_CD : Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) ≤ Nat.card C_D :=
    Nat.card_mono (Set.toFinite _) hCHCK_sub_CD
  have hCHCK_pos : 0 < Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) := by
    rw [Nat.card_pos_iff]
    refine ⟨⟨1, ?_⟩, Set.toFinite _⟩
    exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  -- 積が等しく各因子が `≤` なら各因子が等しい — ここで両方の等号を取る.
  obtain ⟨hHK_eq, hC_eq⟩ :=
    _eq_of_mul_eq_of_le h_cancelled hHK_le_J hCHCK_le_CD Nat.card_pos hCHCK_pos
  exact ⟨(Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hHK_sub_J hHK_eq.symm.le).symm,
    (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hCHCK_sub_CD hC_eq.symm.le).symm⟩

/-- `H, K ∈ L(G)` ならば Lemma 1.43 の不等式は**等号**になる: measure の最大性から
`m_G(D)·m_G(J) ≤ m_G(H)²= m_G(H)·m_G(K)` で、逆向きが 1.43。

Thm 1.44 (a)(b) が共通して使う入口。 -/
theorem chermakDelgadoLattice_measure_mul_eq [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      = (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure := by
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  refine le_antisymm (chermakDelgadoMeasure_mul_le H K) ?_
  calc (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure
      ≤ H.chermakDelgadoMeasure * H.chermakDelgadoMeasure := Nat.mul_le_mul (hH _) (hH _)
    _ = H.chermakDelgadoMeasure * K.chermakDelgadoMeasure := by rw [hsame]

/-- `H, K ∈ L(G)` のとき `m_G(H⊓K) = m_G(H) = m_G(H⊔K)` (Thm 1.44 (a) の中身)。 -/
private theorem _lattice_measure_inf_and_sup_eq [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    (H ⊓ K).chermakDelgadoMeasure = H.chermakDelgadoMeasure ∧
      (H ⊔ K).chermakDelgadoMeasure = H.chermakDelgadoMeasure := by
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  have h_prod_eq : (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure
                 = H.chermakDelgadoMeasure * H.chermakDelgadoMeasure := by
    rw [← chermakDelgadoLattice_measure_mul_eq hH hK, hsame]
  exact _eq_of_mul_eq_sq_of_le h_prod_eq (hH _) (hH _)

/-- **Isaacs Thm 1.44 (a)**: `L(G)` is closed under intersection. -/
theorem chermakDelgadoLattice_inf_mem [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊓ K ∈ chermakDelgadoLattice G := by
  intro L
  rw [(_lattice_measure_inf_and_sup_eq hH hK).1]
  exact hH L

/-- **Isaacs Thm 1.44 (a)**: `L(G)` is closed under join. -/
theorem chermakDelgadoLattice_sup_mem [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊔ K ∈ chermakDelgadoLattice G := by
  intro L
  rw [(_lattice_measure_inf_and_sup_eq hH hK).2]
  exact hH L

/-- **Isaacs Thm 1.44 (b)**: For `H, K ∈ L`: `⟨H, K⟩ = HK` (as sets).

Lemma 1.43 の等号条件 (`chermakDelgadoMeasure_mul_eq_conditions`) の `J = HK` 節そのもの。
`H, K ∈ L` は等号成立 (`chermakDelgadoLattice_measure_mul_eq`) を保証するためだけに使う。 -/
theorem chermakDelgadoLattice_sup_eq_mul [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    ((H ⊔ K : Subgroup G) : Set G) = ↑H * ↑K :=
  (chermakDelgadoMeasure_mul_eq_conditions H K
    (chermakDelgadoLattice_measure_mul_eq hH hK)).1

/-- **Isaacs Lemma 1.42 (equality condition)**: `m_G(H) = m_G(C_G(H))` iff
`C_G(C_G(H)) = H`. Cor 1.45 + Thm 1.44(c) で使用. -/
theorem chermakDelgadoMeasure_eq_centralizer_iff [Finite G] (H : Subgroup G) :
    H.chermakDelgadoMeasure
        = (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure
      ↔ centralizer ((centralizer (H : Set G) : Subgroup G) : Set G) = H := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
  constructor
  · intro h_eq
    -- |H| * |C_H| = |C_H| * |C(C_H)|, |C_H| > 0 ⟹ |H| = |C(C_H)|
    rw [Nat.mul_comm (Nat.card ↥(centralizer (H : Set G) : Subgroup G))
        (Nat.card ↥(centralizer ((centralizer (H : Set G) : Subgroup G) : Set G)))] at h_eq
    have hCH_pos : 0 < Nat.card ↥(centralizer (H : Set G) : Subgroup G) := Nat.card_pos
    have h_card :
        Nat.card ↥H
          = Nat.card ↥(centralizer ((centralizer (H : Set G) : Subgroup G) : Set G)) :=
      Nat.eq_of_mul_eq_mul_right hCH_pos h_eq
    -- H ≤ C(C_H), |H| = |C(C_H)|, finite ⟹ H = C(C_H)
    symm
    apply SetLike.coe_injective
    exact Set.Finite.eq_of_subset_of_card_le (Set.toFinite _)
      (SetLike.coe_subset_coe.mpr H.le_centralizer_centralizer) h_card.ge
  · intro h_eq
    -- C(C(H)) = H ⟹ |H| = |C(C(H))| ⟹ 等式
    rw [show Nat.card ↥H
          = Nat.card ↥(centralizer ((centralizer (H : Set G) : Subgroup G) : Set G)) by rw [h_eq]]
    ring

/-- **Isaacs Thm 1.44 (c)**: For `H ∈ L`: `C_G(H) ∈ L`. -/
theorem chermakDelgadoLattice_centralizer_mem [Finite G] {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    (centralizer (H : Set G) : Subgroup G) ∈ chermakDelgadoLattice G := by
  intro L
  have h_eq : (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure
            = H.chermakDelgadoMeasure :=
    le_antisymm (hH _) (chermakDelgadoMeasure_le_centralizer H)
  rw [h_eq]
  exact hH L

/-- **Isaacs Thm 1.44 (c)**: For `H ∈ L`: `C_G(C_G(H)) = H`. -/
theorem chermakDelgadoLattice_centralizer_centralizer_eq [Finite G] {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    centralizer ((centralizer (H : Set G) : Subgroup G) : Set G) = H := by
  have h_eq : H.chermakDelgadoMeasure
            = (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure :=
    le_antisymm (chermakDelgadoMeasure_le_centralizer H) (hH _)
  exact (chermakDelgadoMeasure_eq_centralizer_iff H).mp h_eq

/-! ### Cor 1.45 + Thm 1.41: properties of `M = chermakDelgadoSubgroup G`. -/

/-- L(G) is nonempty (max measure exists for finite G). -/
theorem chermakDelgadoLattice_nonempty [Finite G] :
    (chermakDelgadoLattice G).Nonempty := by
  have : Nonempty (Subgroup G) := ⟨⊥⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨H_max, h_max⟩ :=
    Finite.exists_max (fun H : Subgroup G => H.chermakDelgadoMeasure)
  exact ⟨H_max, h_max⟩

/-- L(G) is finite. -/
theorem chermakDelgadoLattice_finite [Finite G] :
    (chermakDelgadoLattice G).Finite := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  exact Set.toFinite _

/-- M = sInf L (alternative form of `chermakDelgadoSubgroup`). -/
theorem chermakDelgadoSubgroup_eq_sInf :
    chermakDelgadoSubgroup G = sInf (chermakDelgadoLattice G) := by
  rw [chermakDelgadoSubgroup, sInf_eq_iInf]

/-- 補助: 有限・閉じた sublattice の `sInf` は中身に入っている. -/
private theorem _sInf_mem_of_finite_subset [Finite G] (S : Set (Subgroup G))
    (hfin : S.Finite) :
    S.Nonempty → S ⊆ chermakDelgadoLattice G → sInf S ∈ chermakDelgadoLattice G := by
  induction S, hfin using Set.Finite.induction_on with
  | empty => intro hne _; exact (Set.not_nonempty_empty hne).elim
  | @insert a t hat ht_fin ih =>
    intro _hne hsub
    rcases t.eq_empty_or_nonempty with rfl | ht_ne
    · -- t = ∅, so S = {a}. sInf {a} = a, and a ∈ L
      rw [Set.insert_eq, Set.union_empty, sInf_singleton]
      exact hsub (Set.mem_insert _ _)
    · -- t nonempty
      have hsub_t : t ⊆ chermakDelgadoLattice G :=
        fun H hH => hsub (Set.mem_insert_of_mem _ hH)
      have ha_in : a ∈ chermakDelgadoLattice G := hsub (Set.mem_insert _ _)
      have h_ih := ih ht_ne hsub_t
      rw [sInf_insert]
      exact chermakDelgadoLattice_inf_mem ha_in h_ih

/-- **Isaacs Cor 1.45 part 1**: `M = chermakDelgadoSubgroup G ∈ L(G)`. -/
theorem chermakDelgadoSubgroup_mem_lattice [Finite G] :
    chermakDelgadoSubgroup G ∈ chermakDelgadoLattice G := by
  rw [chermakDelgadoSubgroup_eq_sInf]
  exact _sInf_mem_of_finite_subset _ chermakDelgadoLattice_finite
    chermakDelgadoLattice_nonempty Set.Subset.rfl

/-- `M ≤ H` for any `H ∈ L`. -/
theorem chermakDelgadoSubgroup_le_of_mem [Finite G] {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    chermakDelgadoSubgroup G ≤ H := by
  rw [chermakDelgadoSubgroup_eq_sInf]
  exact sInf_le hH

/-- `M ≤ C_G(M)` ── M ∈ L で `C_G(M) ∈ L` (Thm 1.44(c)) なので `M ≤ C_G(M)`. -/
theorem chermakDelgadoSubgroup_le_centralizer [Finite G] :
    chermakDelgadoSubgroup G
      ≤ (centralizer ((chermakDelgadoSubgroup G : Subgroup G) : Set G) : Subgroup G) :=
  chermakDelgadoSubgroup_le_of_mem
    (chermakDelgadoLattice_centralizer_mem chermakDelgadoSubgroup_mem_lattice)

/-- **Isaacs Cor 1.45 part 2**: `M` is abelian (`IsMulCommutative`). -/
instance chermakDelgadoSubgroup_isMulCommutative [Finite G] :
    IsMulCommutative (chermakDelgadoSubgroup G) :=
  le_centralizer_iff_isMulCommutative.mp chermakDelgadoSubgroup_le_centralizer

/-- **Isaacs Cor 1.45 part 3**: `Z(G) ≤ M`.

`M = C_G(C_G(M))` (Thm 1.44(c)) で `Z(G) ≤ C_G(X)` (任意 X) を組み合わせる. -/
theorem center_le_chermakDelgadoSubgroup [Finite G] :
    center G ≤ chermakDelgadoSubgroup G := by
  rw [← chermakDelgadoLattice_centralizer_centralizer_eq chermakDelgadoSubgroup_mem_lattice]
  exact center_le_centralizer _

/-- Chermak-Delgado 測度は群自己同型の下で不変. -/
private lemma chermakDelgadoMeasure_map_equiv (ϕ : G ≃* G) (K : Subgroup G) :
    (K.map ϕ.toMonoidHom).chermakDelgadoMeasure = K.chermakDelgadoMeasure := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
  have h_card_K : Nat.card (K.map ϕ.toMonoidHom : Subgroup G) = Nat.card K :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective K ϕ.toMonoidHom ϕ.injective).symm.toEquiv
  have h_centralizer :
      (centralizer ((K.map ϕ.toMonoidHom : Subgroup G) : Set G) : Subgroup G)
        = (centralizer (K : Set G) : Subgroup G).map ϕ.toMonoidHom := by
    apply SetLike.coe_injective
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, mem_centralizer_iff, SetLike.mem_coe]
    constructor
    · intro hg
      refine ⟨ϕ.symm g, ?_, by simp⟩
      intro k hk
      -- hg (ϕ k) hkmap : ϕ k * g = g * ϕ k
      have h1 : ϕ k * g = g * ϕ k :=
        hg (ϕ k) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
      have h2 := congrArg ϕ.symm h1
      simp only [MulEquiv.map_mul, MulEquiv.symm_apply_apply] at h2
      -- h2 : k * ϕ.symm g = ϕ.symm g * k
      exact h2
    · rintro ⟨a, ha, rfl⟩ y hy
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
      -- ha k hk : k * a = a * k
      have h1 : k * a = a * k := ha k hk
      have h2 := congrArg ϕ h1
      simp only [MulEquiv.map_mul] at h2
      -- h2 : ϕ k * ϕ a = ϕ a * ϕ k
      exact h2
  rw [h_card_K, h_centralizer]
  congr 1
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective
      (centralizer (K : Set G) : Subgroup G) ϕ.toMonoidHom ϕ.injective).symm.toEquiv

/-- comap 版の不変性. -/
private lemma chermakDelgadoMeasure_comap_equiv (ϕ : G ≃* G) (K : Subgroup G) :
    (K.comap ϕ.toMonoidHom).chermakDelgadoMeasure = K.chermakDelgadoMeasure := by
  rw [comap_equiv_eq_map_symm', chermakDelgadoMeasure_map_equiv]

/-- 自己同型は L(G) を保つ (comap 形式). -/
private lemma chermakDelgadoLattice_comap_mem (ϕ : G ≃* G) {K : Subgroup G}
    (hK : K ∈ chermakDelgadoLattice G) :
    K.comap ϕ.toMonoidHom ∈ chermakDelgadoLattice G := by
  intro J
  rw [chermakDelgadoMeasure_comap_equiv]
  exact hK J

/-- **Isaacs Cor 1.45 part 4**: `M` is characteristic.

`L(G)` は自己同型で不変 ⟹ `M = sInf L(G)` も不変. -/
instance chermakDelgadoSubgroup_characteristic [Finite G] :
    (chermakDelgadoSubgroup G).Characteristic := by
  rw [characteristic_iff_le_comap]
  intro ϕ
  rw [chermakDelgadoSubgroup_eq_sInf]
  -- 目標: sInf L ≤ (sInf L).comap ϕ
  -- 各 x ∈ sInf L について, ϕ x ∈ sInf L を示せばよい
  intro x hx
  rw [mem_comap, Subgroup.mem_sInf]
  intro K hK
  -- K ∈ L. ϕ x ∈ K ↔ x ∈ K.comap ϕ. K.comap ϕ ∈ L (measure-invariant).
  -- x ∈ sInf L ≤ K.comap ϕ. ✓
  have hKcomap : K.comap ϕ.toMonoidHom ∈ chermakDelgadoLattice G :=
    chermakDelgadoLattice_comap_mem ϕ hK
  rw [Subgroup.mem_sInf] at hx
  exact hx _ hKcomap

/-! ### Thm 1.41 (Chermak-Delgado main theorem). -/

/-- **Isaacs Thm 1.41 (Chermak-Delgado)**: There exists a characteristic abelian subgroup `N` with
`|G : N| ≤ |G : A|²` for every abelian subgroup `A`.

具体的には `N = chermakDelgadoSubgroup G` を取る. -/
theorem chermakDelgado [Finite G] :
    ∃ N : Subgroup G, N.Characteristic ∧ IsMulCommutative N ∧
      ∀ A : Subgroup G, IsMulCommutative A → N.index ≤ A.index ^ 2 := by
  refine ⟨chermakDelgadoSubgroup G, inferInstance, inferInstance, ?_⟩
  intro A hA
  set M := chermakDelgadoSubgroup G with hM_def
  -- Step 1: |A| ≤ |C_G(A)| (since A ≤ C_G(A) for abelian A)
  have : IsMulCommutative A := hA
  have hA_le_CA : Nat.card A ≤ Nat.card (centralizer (A : Set G) : Subgroup G) :=
    Nat.card_le_card_of_injective
      (Subgroup.inclusion A.le_centralizer) (Subgroup.inclusion_injective _)
  -- Step 2: |A|² ≤ m_G(A) = |A|·|C_G(A)|
  have hA_sq_le : Nat.card A ^ 2 ≤ A.chermakDelgadoMeasure := by
    rw [chermakDelgadoMeasure_def, sq]
    exact Nat.mul_le_mul_left _ hA_le_CA
  -- Step 3: m_G(A) ≤ m_G(M) (M ∈ L)
  have hA_le_M : A.chermakDelgadoMeasure ≤ M.chermakDelgadoMeasure :=
    chermakDelgadoSubgroup_mem_lattice A
  have hA_sq_le_M : Nat.card A ^ 2 ≤ M.chermakDelgadoMeasure := hA_sq_le.trans hA_le_M
  -- Step 4: Lagrange |G| = |M|·M.index = |A|·A.index
  have hM_card : Nat.card M * M.index = Nat.card G := M.card_mul_index
  have hA_card : Nat.card A * A.index = Nat.card G := A.card_mul_index
  -- Step 5: |G|² = |A|² · A.index² (rearrange Lagrange)
  have hG_sq : Nat.card G ^ 2 = Nat.card A ^ 2 * A.index ^ 2 := by
    rw [← hA_card]; ring
  -- Step 6: M.index · |A|² ≤ M.index · m_G(M) = |G| · |C_G(M)| ≤ |G|²
  have h1 : M.index * Nat.card A ^ 2 ≤ M.index * M.chermakDelgadoMeasure :=
    Nat.mul_le_mul_left _ hA_sq_le_M
  have h2 : M.index * M.chermakDelgadoMeasure
          = Nat.card G * Nat.card (centralizer (M : Set G) : Subgroup G) := by
    rw [chermakDelgadoMeasure_def]
    -- M.index · (|M| · |C_G(M)|) = (M.index · |M|) · |C_G(M)| = (|M| · M.index) · |C_G(M)|
    rw [← Nat.mul_assoc, Nat.mul_comm M.index (Nat.card M), hM_card]
  have h3 : Nat.card (centralizer (M : Set G) : Subgroup G) ≤ Nat.card G :=
    Nat.card_le_card_of_injective
      (centralizer (M : Set G) : Subgroup G).subtype
      ((centralizer (M : Set G) : Subgroup G).subtype_injective)
  have h4 : Nat.card G * Nat.card (centralizer (M : Set G) : Subgroup G) ≤ Nat.card G ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_left _ h3
  have h5 : M.index * Nat.card A ^ 2 ≤ Nat.card G ^ 2 := h1.trans (h2.le.trans h4)
  -- Step 7: |G|² = |A|² · A.index² ⟹ M.index · |A|² ≤ A.index² · |A|²
  rw [hG_sq, Nat.mul_comm (Nat.card A ^ 2) (A.index ^ 2)] at h5
  -- Step 8: Cancel |A|² (positive)
  exact Nat.le_of_mul_le_mul_right h5 (pow_pos Nat.card_pos 2)

/-! ### Cor 1.46. -/

/-- **Isaacs Cor 1.46**: If `H ≤ G` with `|H| · |C_G(H)| > |G|`, then `G` is not a nonabelian simple
group. -/
theorem not_isSimpleGroup_and_nonabelian_of_chermakDelgadoMeasure_gt [Finite G]
    {H : Subgroup G} (h : H.chermakDelgadoMeasure > Nat.card G) :
    ¬ (IsSimpleGroup G ∧ ¬ IsMulCommutative G) := by
  rintro ⟨h_simple, h_nonab⟩
  set M := chermakDelgadoSubgroup G with hM_def
  -- m_G(M) > |G|
  have h_M_gt : Nat.card G < M.chermakDelgadoMeasure :=
    lt_of_lt_of_le h (chermakDelgadoSubgroup_mem_lattice H)
  -- m_G(⊥) = |G|
  have h_bot_measure : (⊥ : Subgroup G).chermakDelgadoMeasure = Nat.card G := by
    rw [chermakDelgadoMeasure_def, Subgroup.card_bot, one_mul]
    have hC : (centralizer ((⊥ : Subgroup G) : Set G) : Subgroup G) = ⊤ := by
      ext x
      rw [Subgroup.coe_bot]
      simp [mem_centralizer_iff]
    rw [hC]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  -- M ≠ ⊥
  have h_M_ne_bot : M ≠ ⊥ := by
    intro h_eq
    rw [h_eq, h_bot_measure] at h_M_gt
    exact (lt_irrefl _) h_M_gt
  -- M is normal (characteristic ⟹ normal)
  have : M.Normal := inferInstance
  -- G simple ⟹ M = ⊥ or M = ⊤. M ≠ ⊥ ⟹ M = ⊤
  have h_M_top : M = ⊤ :=
    (h_simple.eq_bot_or_eq_top_of_normal M).resolve_left h_M_ne_bot
  -- M abelian
  have hM_comm : IsMulCommutative M := inferInstance
  -- IsMulCommutative G derivation
  apply h_nonab
  refine ⟨⟨fun a b => ?_⟩⟩
  have h_top_comm := h_M_top ▸ hM_comm
  exact congrArg Subtype.val
    (h_top_comm.is_comm.comm
      (⟨a, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) ⟨b, Subgroup.mem_top _⟩)

end Subgroup
end

/-! ### Module `OddOrder.Isaacs.Ch01_Sylow.Basic` -/
section
/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# Basic

Prefix-split from `OddOrder.Isaacs.Ch01_Sylow.Main` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# OddOrder.Isaacs.Ch01 — Sylow Theory

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 1
"Sylow Theory" (pp. 1-44) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 1A | 群作用と Fundamental Counting Principle | 1.1 – 1.6 | ✅ 被覆 (1.1/1.5/1.6 は mathlib) |
| 1B | Sylow の存在定理 (Sylow E), Cauchy | 1.7 – 1.10 | ✅ 被覆 (1.7/1.10 は mathlib) |
| 1C | Sylow の共役 (Sylow C / D), Frattini | 1.11 – 1.18 | ✅ 被覆 (多くは mathlib) |
| 1D | 冪零群, Fitting 部分群 `F(G)` | 1.19 – 1.29 | ✅ 被覆 (1.24 は 2026-08-08 に正規条項を補充) |
| 1E | 位数 \|G\|=2n (n 奇) の指数 2 正規部分群 など | 1.30 – 1.36 | ✅ 被覆 |
| 1F | Brodkey の定理 (Sylow が abelian の場合) | 1.37 – 1.40 | ✅ 被覆 |
| 1G | Chermak–Delgado | 1.41 – 1.46 | ✅ 被覆 (`GroupTheory/ChermakDelgado.lean`) |

⚠ この表は 2026-08-08 の逐条監査 (issue 0176) で更新した。それ以前は 1A が「着手中」、
1B/1C/1D/1E/1G が「TODO」のままで、章が広範に形式化された後も**放置されていた** —
`notes/isaacs/full_formalization_census_2026_08_08.md` の「stale な自己注記」型そのもの。
mathlib 被覆分を含む番号ごとの対応は同 census note が正本。

## 方針

mathlib 既存資産 (`Sylow`, `MulAction.orbitEquivQuotientStabilizer`,
`Subgroup.normalCore`, `Subgroup.normalCore_eq_ker`) を最大限再利用し、
Isaacs の流儀で主張を再述する薄いラッパーを与える。

主要な新規実装ターゲット (mathlib 未収載):

* **§1D Thm 1.28**: Fitting 部分群 `Fit(G)` の定義 + 「最大冪零正規部分群である」
  ことの証明 (Phase 1 の最初の本格的な新規実装)

ノート: [notes/isaacs/ch01_sylow.md](../../notes/isaacs/ch01_sylow.md)
-/

namespace OddOrder.Isaacs.Ch01

open scoped IsMulCommutative

section /- 1A: Group actions and the Fundamental Counting Principle (pp. 1-10) -/

open scoped Pointwise

variable {G : Type*} [Group G]

/-! **Isaacs Thm 1.1** (`H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker`) と
**Thm 1.4** (`MulAction.orbit G α ≃ G ⧸ MulAction.stabilizer G α`) は mathlib
`Subgroup.normalCore_eq_ker` / `MulAction.orbitEquivQuotientStabilizer` を直接
呼び出す (本ファイルではラッパーを書かない). -/

/-! **Isaacs Cor 1.5** (`|conjClass x| = [G : C_G(x)]`) と **Cor 1.6**
(`|conj(H)| = [G : N_G(H)]`) は mathlib の `ConjAct.orbit_eq_carrier_conjClasses` +
`MulAction.index_stabilizer` + `Subgroup.centralizer_eq_comap_stabilizer` を
直接組合せる. -/

end -- 1A

section /- 1B: Sylow's existence theorem and Cauchy (pp. 10-17) -/

variable {G : Type*} [Group G]

/-! **Isaacs Thm 1.7** (Sylow E) は mathlib `Sylow.nonempty` を直接呼ぶ.
**Lemma 1.8** (`C(p^a m, p^a) ≡ m mod p`) は
`Choose.choose_pow_mul_pow_mul_modEq_choose_nat (b := 1)` を直接呼ぶ. -/

/-! **Isaacs Lemma 1.10** (特性 in 正規 ⇒ 正規) は mathlib
`Subgroup.normal_of_characteristic_of_normal` がインスタンスとして提供している
ので typeclass で自動推論される. 呼び出し側では `inferInstance` で取得. -/

end -- 1B

section /- 1C: Sylow C / D, Frattini argument (pp. 13-17) -/

open Pointwise Subgroup MulAction

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-! **Isaacs Thm 1.11** (任意 `p`-部分群は Sylow の共役に含まれる),
**Thm 1.12 Sylow C** (任意 2 Sylow が共役),
**Lemma 1.13 Frattini argument**,
**Thm 1.14 Sylow D** (任意 `p`-部分群は Sylow に含まれる),
**Cor 1.15** (`n_p(G) = [G : N_G(S)]`) はすべて mathlib に直接対応がある:

* Thm 1.11: `IsPGroup.exists_le_sylow` + `Sylow.orbit_eq_top` を組合せる
* Thm 1.12: `MulAction.exists_smul_eq` (`Sylow.isPretransitive_of_finite`)
* Lemma 1.13: `Sylow.normalizer_sup_eq_top'`
* Thm 1.14: `IsPGroup.exists_le_sylow`
* Cor 1.15: `Sylow.card_eq_index_normalizer`

呼び出し側で直接 mathlib 名を使う. -/

/-! **Isaacs Cor 1.17** (`n_p ≡ 1 mod p`) は mathlib `card_sylow_modEq_one` を,
**Lemma 1.18** (`N_G(P)` 内の `p`-部分群は `P` に含まれる) は
`IsPGroup.inf_normalizer_sylow` を直接呼ぶ. -/

end -- 1C

section /- 1D: Nilpotent groups, Fitting subgroup F(G) (pp. 21-29) -/

open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Isaacs Thm 1.19–1.25: 冪零群と p-群の基本構造 -/

/-! **Isaacs Lemma 1.20** は冪零性のいくつかの特性化を主張するが, (1)-(2) は
`IsNilpotent` の定義そのもの, (3) 「全 Sylow 正規」は mathlib
`Group.isNilpotent_of_finite_tfae` 全体に対応する (Thm 1.26 慣用名
`isNilpotent_iff_forall_sylow_normal` で扱う).

**Thm 1.20** (冪零 ⇔ NormalizerCondition) は `Group.isNilpotent_of_finite_tfae.out 1 2`,
**Thm 1.21** (`upperCentralSeries G (nilpotencyClass G) = ⊤`) は
`upperCentralSeries_nilpotencyClass` を直接呼ぶ. -/

/-! ### O_p(G) と Fitting 部分群 F(G)

Isaacs §1D 後半の主要新規実装。詳細設計は
[notes/isaacs/ch01_sylow_d_fitting.md](../../notes/isaacs/ch01_sylow_d_fitting.md)。

`opCore p G` (= `O_p(G)`) は全 Sylow `p`-部分群の共通部分として定義し,
最大の正規 `p`-部分群であることを示す (Isaacs Problem 1B.2). この上に
`fitting G` (= `F(G)`) を `⨆_{p prime} opCore p G` として乗せる. -/

/-- `O_p(G)`: `G` の全 Sylow `p`-部分群の共通部分.  Isaacs Problem 1B.2 で示される
ように, これは `G` の最大の正規 `p`-部分群と一致する.

mathlib 未収載のため新規定義 (将来 mathlib に `Subgroup.opCore` として PR したい形). -/
def opCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ P : Sylow p G, (P : Subgroup G)

@[simp]
theorem mem_opCore {p : ℕ} {x : G} :
    x ∈ opCore p G ↔ ∀ P : Sylow p G, x ∈ (P : Subgroup G) := by
  simp [opCore, Subgroup.mem_iInf]

theorem opCore_le {p : ℕ} (P : Sylow p G) : opCore p G ≤ (P : Subgroup G) :=
  iInf_le _ P

/-- `O_p(G)` は `p`-部分群 (Sylow に含まれるから).

`[Fact p.Prime]` 必須 (`Sylow.nonempty` から少なくとも 1 つの Sylow を取るため). -/
theorem opCore_isPGroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] :
    IsPGroup p (opCore p G) := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  exact P.2.of_injective (Subgroup.inclusion (opCore_le P))
    (Subgroup.inclusion_injective _)

/-- `O_p(G)` は `G` で正規.
証明: `Subgroup.Normal.of_conjugate_fixed` を使い,
`∀ g : G, MulAut.conj g • opCore p G = opCore p G` を示す.
各 `g` について `MulAut.conj g` は Sylow 部分群を Sylow 部分群に写す (`g • P ∈ Sylow p G`)
ので, 全 Sylow の共通部分 `opCore p G` も共役不変. -/
instance opCore.normal (p : ℕ) (G : Type*) [Group G] : (opCore p G).Normal := by
  apply Subgroup.Normal.of_conjugate_fixed
  intro g
  ext x
  simp only [mem_opCore, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  -- After simp: ∀ P, (MulAut.conj g)⁻¹ x ∈ ↑P  ↔  ∀ P, x ∈ ↑P
  -- Here ↑P is the Subgroup G coercion via CoeOut (Sylow p G) (Subgroup G)
  constructor
  · intro h P
    -- Apply h to (g⁻¹ • P : Sylow p G); then unfold the smul at Subgroup level
    have hQ : (MulAut.conj g)⁻¹ x ∈ (↑(g⁻¹ • P) : Subgroup G) := h (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, ← map_inv,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQ
    simp only [map_inv, inv_inv, MulAut.smul_def] at hQ
    rwa [MulAut.apply_inv_self] at hQ
  · intro h P
    -- Apply h to (g • P : Sylow p G); then unfold the smul at Subgroup level
    have hQ : x ∈ (↑(g • P) : Subgroup G) := h (g • P)
    rw [Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQ
    exact hQ

/-- `O_p(G)` は `G` で特性的 (任意の自己同型 `φ : G ≃* G` で不変).

証明: `characteristic_iff_le_comap` 経由. 任意の `φ` と `x ∈ opCore p G` について,
全 Sylow `Q` に対し `Q.comapOfInjective φ.toMonoidHom` も Sylow `p` で,
`x ∈ Q.comapOfInjective ...` ⇔ `φ x ∈ Q`. -/
instance opCore.characteristic (p : ℕ) (G : Type*) [Group G] :
    (opCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  rw [Subgroup.mem_comap, mem_opCore]
  rw [mem_opCore] at hx
  intro Q
  have hinj : Function.Injective (φ.toMonoidHom : G →* G) := φ.injective
  have hrange : (Q : Subgroup G) ≤ (φ.toMonoidHom : G →* G).range := by
    rw [MonoidHom.range_eq_top.mpr φ.surjective]; exact le_top
  -- `Q.comapOfInjective φ.toMonoidHom hinj hrange : Sylow p G` and its coercion is `Q.comap φ`.
  have hxQ' := hx (Q.comapOfInjective (φ.toMonoidHom : G →* G) hinj hrange)
  rwa [Sylow.coe_comapOfInjective, Subgroup.mem_comap] at hxQ'

/-- **Isaacs Problem 1B.2**. 任意の正規 `p`-部分群 `N` は `opCore p G` に含まれる.
これにより `opCore p G` は `G` の最大正規 `p`-部分群である.

証明: Sylow D (`IsPGroup.exists_le_sylow`) で `N ≤ Q` となる Sylow `Q` を取り,
任意の Sylow `P` に対して Sylow C (`[Finite (Sylow p G)]`) で `∃ g, P = g • Q` を取る.
`N` の正規性から `N = MulAut.conj g • N ≤ MulAut.conj g • Q = ↑(g • Q) = ↑P`. -/
theorem normal_pgroup_le_opCore {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite (Sylow p G)]
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p N) :
    N ≤ opCore p G := by
  rw [opCore, le_iInf_iff]
  intro P
  obtain ⟨Q, hNQ⟩ := hN.exists_le_sylow
  obtain ⟨g, hgQ⟩ := MulAction.exists_smul_eq G Q P
  calc (N : Subgroup G)
      = MulAut.conj g • N := (Subgroup.Normal.conj_smul_eq_self g N).symm
    _ ≤ MulAut.conj g • (Q : Subgroup G) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNQ
    _ = ↑(g • Q) := Sylow.coe_subgroup_smul.symm
    _ = ↑P := by rw [hgQ]

/-! ### Isaacs Thm 1.26 (冪零 ⇔ Sylow 全正規) -/

/-- **Isaacs Thm 1.26 (1) ⇔ (4)**.  有限群 `G` について「`G` が冪零」と
「`G` の任意の Sylow 部分群が正規」は同値.

mathlib `Group.isNilpotent_of_finite_tfae` の (0) ⇔ (3) の抽出ラッパー.  Isaacs 流 5 条件
((1)冪零, (2)`H<G ⇒ N_G(H)>H`, (3) 全極大正規, (4) 全 Sylow 正規, (5) Sylow 内部直積)
は TFAE 全体 (`Group.isNilpotent_of_finite_tfae`) で確保される. -/
theorem isNilpotent_iff_forall_sylow_normal [Finite G] :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G), (↑P : Subgroup G).Normal :=
  Group.isNilpotent_of_finite_tfae.out 1 4

/-! **Isaacs Thm 1.26 (4) ⇒ (1)** (全 Sylow 正規 ⇒ 冪零) は呼出側で
`isNilpotent_iff_forall_sylow_normal.mpr` を直接呼ぶ. -/

/-- **Isaacs Thm 1.26 (1) ⇒ (4)** (片向き取り出し).
冪零ならば任意の Sylow は正規. -/
theorem Sylow.normal_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) : (↑P : Subgroup G).Normal :=
  isNilpotent_iff_forall_sylow_normal.mp ‹_› p P

/-! ### Fitting 部分群 F(G) -/

/-- **Fitting subgroup** `F(G)`: 全ての素数 `p` についての `opCore p G` (= `O_p(G)`)
の supremum.  これは `G` の最大の正規冪零部分群となる (Isaacs Cor 1.28).

mathlib 未収載のため新規定義. `Subgroup.fitting` として将来 mathlib に PR したい形.

Isaacs 流の定義「`|G|` の各素因子 `p` について `O_p(G)` の積」と等価. 非素数 `p` や
`|G|` に分割しない素数 `p` に対しては `opCore p G ⊆` 既存の sup なので, 範囲を
広げても結果は変わらない (実際 `opCore p G = ⊥` for primes p ∤ |G|, 有限 G で). -/
def fitting (G : Type*) [Group G] : Subgroup G :=
  ⨆ p : Nat.Primes, opCore (p : ℕ) G

theorem opCore_le_fitting (p : Nat.Primes) (G : Type*) [Group G] :
    opCore (p : ℕ) G ≤ fitting G :=
  le_iSup (fun q : Nat.Primes => opCore (q : ℕ) G) p

/-- `F(G)` は `G` で特性的. 各 `opCore p G` が特性的 (`opCore.characteristic`) で,
特性的部分群の sup は特性的 (`Subgroup.map_iSup` + `iSup_congr`). -/
instance fitting.characteristic (G : Type*) [Group G] : (fitting G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  change (⨆ p : Nat.Primes, opCore (p : ℕ) G).map φ.toMonoidHom
    = ⨆ p : Nat.Primes, opCore (p : ℕ) G
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ =>
    Subgroup.characteristic_iff_map_eq.mp (opCore.characteristic _ _) φ

/-- `F(G)` は `G` の正規部分群. 各 `opCore p G` の正規性を `iSup_induction` で全体に持ち上げる. -/
instance fitting.normal (G : Type*) [Group G] : (fitting G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ fitting G) hn
    ?mem ?one ?mul
  case mem =>
    intro p x hx
    -- x ∈ opCore p G が正規だから g * x * g⁻¹ ∈ opCore p G ≤ fitting
    exact (opCore_le_fitting p G) ((opCore.normal (p : ℕ) G).conj_mem x hx g)
  case one =>
    simp
  case mul =>
    intro x y hx hy
    -- g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (fitting G).mul_mem hx hy

/-- 補助補題: 有限冪零群 `N` では, 各素因数 `p` に対する代表 Sylow 部分群
`default : Sylow p N` の supremum は `⊤_N` に等しい.

証明骨子: Thm 1.26 で全 Sylow が正規, よって `unique_of_normal` で各素因数につき
Sylow が 1 つ. `noncommPiCoprod` 経由で `(∀ p ∈ pf(|N|), Sylow p N) →* N` を作り,
互いに素な p-群より単射 (`independent_of_coprime_order`), 濃度比較で全射 ⇒ range = ⊤.
range = `⨆ p, ↑(default Sylow)` (by `noncommPiCoprod_range`). -/
theorem iSup_default_sylow_eq_top_of_nilpotent
    (N : Type*) [Group N] [Finite N] [Group.IsNilpotent N] :
    ⨆ p : (Nat.card N).primeFactors,
        ((default : Sylow (p : ℕ) N) : Subgroup N) = ⊤ := by
  classical
  have hnormal : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p N), P.Normal := fun P =>
    Sylow.normal_of_isNilpotent P
  have _ := Fintype.ofFinite N
  set ps := (Nat.card N).primeFactors with hps
  let P : ∀ p, Sylow p N := default
  have hPfin : ∀ p, Fintype (P p) := fun p ↦ Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps =>
      ∀ x y : N, x ∈ (P p₁ : Subgroup N) → y ∈ (P p₂ : Subgroup N) → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hnormal (P p₁)) (hnormal (P p₂))
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  -- noncommPiCoprod : (∀ p : ps, P p) →* N
  set f := Subgroup.noncommPiCoprod (G := N) (H := fun p : ps => (P p : Subgroup N)) hcomm
    with hf
  -- f is injective by independent_of_coprime_order
  have hinj : Function.Injective f := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  -- |∀ p : ps, P p| = |N|
  have hcard : Fintype.card (∀ p : ps, P p) = Fintype.card N := by
    simp only [← Nat.card_eq_fintype_card]
    calc Nat.card (∀ p : ps, P p)
        = ∏ p : ps, Nat.card (P p) := Nat.card_pi
      _ = ∏ p : ps, p.1 ^ (Nat.card N).factorization p.1 := by
          refine Finset.prod_congr rfl ?_
          rintro ⟨p, hp⟩ _
          exact @Sylow.card_eq_multiplicity _ _ _ p
            ⟨Nat.prime_of_mem_primeFactors hp⟩ (P p)
      _ = ∏ p ∈ ps, p ^ (Nat.card N).factorization p :=
          Finset.prod_finset_coe (fun p => p ^ (Nat.card N).factorization p) _
      _ = (Nat.card N).factorization.prod (· ^ ·) := rfl
      _ = Nat.card N := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'
  -- bijective
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  -- range = ⊤
  have hrange : f.range = (⊤ : Subgroup N) :=
    MonoidHom.range_eq_top.mpr hbij.surjective
  -- but noncommPiCoprod_range says range = ⨆ i, H i
  have hrange' : f.range = ⨆ p : ps, (P p : Subgroup N) :=
    Subgroup.noncommPiCoprod_range
  rw [hrange'] at hrange
  exact hrange

/-- **Isaacs Cor 1.28(b)** (Fitting subgroup の最大性).
任意の正規冪零部分群 `N` は `fitting G` に含まれる.

証明骨子: `N` が冪零 ⇒ `N` の各 Sylow `Q` は `N` で正規 (Thm 1.26) ⇒ `Q` は `N` で
特性的 (`Sylow.characteristic_of_normal`) ⇒ `N ◁ G` で `Q.map N.subtype ◁ G` (Lemma 1.10).
これが `p`-部分群なので Problem 1B.2 で `Q.map N.subtype ≤ opCore p G ≤ fitting G`.
`N` 全体が unique Sylow 達の sup に等しい (`iSup_default_sylow_eq_top_of_nilpotent`) ことから
`N ≤ fitting G`. -/
theorem nilpotent_normal_le_fitting [Finite G] {N : Subgroup G} [N.Normal]
    [Group.IsNilpotent N] : N ≤ fitting G := by
  -- N 全体 (= ⊤ within Subgroup N, mapped through N.subtype = N) ≤ fitting G
  have hsup : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hsup, ← iSup_default_sylow_eq_top_of_nilpotent N, Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  have hp' : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  -- default : Sylow p N is normal in N
  have hPN : (default : Sylow p N).Normal := Sylow.normal_of_isNilpotent _
  -- default Sylow is characteristic in N (unique Sylow ⇒ characteristic)
  have : ((default : Sylow p N) : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal _ hPN
  -- so its image in G is normal (mathlib instance: characteristic in normal ⇒ normal)
  have : (((default : Sylow p N) : Subgroup N).map N.subtype).Normal :=
    inferInstance
  -- it's a p-subgroup of G
  have hpGroup : IsPGroup p (((default : Sylow p N) : Subgroup N).map N.subtype) :=
    (default : Sylow p N).2.map N.subtype
  -- Problem 1B.2 + opCore ≤ fitting
  calc ((default : Sylow p N) : Subgroup N).map N.subtype
      ≤ opCore p G := normal_pgroup_le_opCore hpGroup
    _ ≤ fitting G := opCore_le_fitting ⟨p, hp'.out⟩ G

/-- 有限 `G` で `p ∤ |G|` (より一般に `p` が `|G|` の素因子でない) なら, 任意の
Sylow `p`-部分群は自明 `⊥`, 従って `opCore p G = ⊥`.

`Sylow.card_eq_multiplicity` で各 Sylow の濃度は `p ^ v_p(|G|)`. `p ∉ pf(|G|)` なら
`v_p(|G|) = 0` で濃度 1, ゆえ `⊥`. -/
theorem opCore_eq_bot_of_not_mem_primeFactors [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ∉ (Nat.card G).primeFactors) :
    opCore p G = ⊥ := by
  -- Pick any Sylow P; it's ⊥ since its card is p^0 = 1.
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hcard : Nat.card (P : Subgroup G) = 1 := by
    rw [Sylow.card_eq_multiplicity P]
    have hfact : (Nat.card G).factorization p = 0 := by
      by_cases hdvd : p ∣ Nat.card G
      · -- p divides but is not in primeFactors → contradiction since Nat.card G ≠ 0
        exfalso
        exact hp (Nat.mem_primeFactors.mpr
          ⟨(Fact.out : p.Prime), hdvd, Nat.card_pos.ne'⟩)
      · exact Nat.factorization_eq_zero_of_not_dvd hdvd
    rw [hfact, pow_zero]
  have hPbot : (P : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  exact le_bot_iff.mp (le_of_le_of_eq (opCore_le P) hPbot)

/-- 有限 `G` について `fitting G` は `|G|` の素因子だけに渡る `opCore` の sup と等しい.
非素因子 `p` に対しては `opCore p G = ⊥` で寄与しないため. -/
theorem fitting_eq_iSup_primeFactors [Finite G] :
    fitting G = ⨆ p : (Nat.card G).primeFactors, opCore (p : ℕ) G := by
  apply le_antisymm
  · -- fitting = ⨆ p : Primes ≤ ⨆ p : pf
    refine iSup_le (fun p => ?_)
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    by_cases hmem : (p : ℕ) ∈ (Nat.card G).primeFactors
    · -- p is in primeFactors, contribute via the indexed sup
      exact le_iSup (fun q : (Nat.card G).primeFactors => opCore (q : ℕ) G) ⟨p, hmem⟩
    · -- p not in primeFactors: opCore p G = ⊥
      rw [opCore_eq_bot_of_not_mem_primeFactors hmem]
      exact bot_le
  · -- ⨆ p : pf ≤ ⨆ p : Primes (= fitting)
    refine iSup_le (fun p => ?_)
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    exact opCore_le_fitting ⟨(p : ℕ), hp⟩ G

/-- **Isaacs Cor 1.28(a)** (Fitting subgroup の冪零性).
有限群 `G` について `fitting G` は冪零.

証明骨子: `(Nat.card G).primeFactors` 上の積 `∀ p, opCore p G` から `G` への
`noncommPiCoprod` を考える. (i) 異なる素数 `p ≠ q` で `opCore p G, opCore q G` は
互いに素な p-群 (`IsPGroup.disjoint_of_ne`) ゆえ可換 (`commute_of_normal_of_disjoint`,
両者は正規), (ii) `independent_of_coprime_order` で `iSupIndep`, よって
`noncommPiCoprod` は単射 (`injective_noncommPiCoprod_of_iSupIndep`).
range は `⨆ p, opCore p G = fitting G` (`fitting_eq_iSup_primeFactors`).
従って `(∀ p, opCore p G) ≃* fitting G` (`MulEquiv.ofInjective` + `subgroupCongr`).
各 `opCore p G` は有限 p-群ゆえ冪零 (`IsPGroup.isNilpotent`), 有限積も冪零
(`Group.isNilpotent_pi`), `MulEquiv` で `fitting G` も冪零.

`instance` 指定で `[Group.IsNilpotent (fitting G)]` が下流で自動推論される. -/
instance fitting.isNilpotent [Finite G] : Group.IsNilpotent (fitting G) := by
  classical
  have _ := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors with hps
  -- For each p ∈ pf, opCore p G is a p-group and normal in G
  have hcomm : Pairwise fun p₁ p₂ : ps =>
      ∀ x y : G, x ∈ opCore (p₁ : ℕ) G → y ∈ opCore (p₂ : ℕ) G → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' : Fact (p₁ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    have hp₂' : Fact (p₂ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (opCore.normal p₁ G)
      (opCore.normal p₂ G)
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _
      (opCore_isPGroup p₁ G) (opCore_isPGroup p₂ G)
  set f := Subgroup.noncommPiCoprod (G := G)
    (H := fun p : ps => opCore (p : ℕ) G) hcomm with hf
  -- f is injective by iSupIndep (coprime orders)
  have hinj : Function.Injective f := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' : Fact (p₁ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    have hp₂' : Fact (p₂ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _
      (opCore_isPGroup p₁ G) (opCore_isPGroup p₂ G)
  -- range f = ⨆ p, opCore p G = fitting G
  have hrange : f.range = fitting G := by
    rw [hf, Subgroup.noncommPiCoprod_range, ← fitting_eq_iSup_primeFactors]
  -- Build MulEquiv (∀ p, opCore p G) ≃* fitting G
  let e : (∀ p : ps, opCore (p : ℕ) G) ≃* fitting G :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  -- Each opCore p G (as a group) is finite + p-group ⇒ nilpotent
  have hnilp : ∀ p : ps, Group.IsNilpotent (opCore (p : ℕ) G) := by
    rintro ⟨p, hp⟩
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact (opCore_isPGroup p G).isNilpotent
  -- Finite product of nilpotent is nilpotent
  have : ∀ p : ps, Group.IsNilpotent (opCore (p : ℕ) G) := hnilp
  have : Group.IsNilpotent (∀ p : ps, opCore (p : ℕ) G) := Group.isNilpotent_pi
  -- Transport across the MulEquiv
  exact Group.nilpotent_of_mulEquiv e

/-- **Isaacs Cor 1.29** (冪零正規部分群の積も冪零).
`K, L` が `G` の正規冪零部分群ならば `K ⊔ L` (= `KL`) も冪零.

証明: Cor 1.28(b) で `K, L ≤ fitting G` ⇒ `K ⊔ L ≤ fitting G`.
`(K ⊔ L).subgroupOf (fitting G)` は冪零 (Cor 1.28(a) + `Subgroup.isNilpotent` instance),
`subgroupOfEquivOfLe` の同型で `K ⊔ L` も冪零. -/
instance sup_isNilpotent_of_normal_nilpotent [Finite G]
    (K L : Subgroup G) [K.Normal] [L.Normal]
    [Group.IsNilpotent K] [Group.IsNilpotent L] :
    Group.IsNilpotent (↥(K ⊔ L)) := by
  have hKLfit : K ⊔ L ≤ fitting G :=
    sup_le nilpotent_normal_le_fitting nilpotent_normal_le_fitting
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKLfit)

end -- 1D

section /- 1E: Small-order groups, normal subgroup of index 2 (pp. 31-34) -/

open scoped Pointwise

variable {G : Type*} [Group G]

end
end OddOrder.Isaacs.Ch01
end

/-! ### Module `OddOrder.Isaacs.Ch01_Sylow.Theorem131` -/
section
/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# Theorem131

Prefix-split from `OddOrder.Isaacs.Ch01_Sylow.Main` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Isaacs.Ch01
open scoped IsMulCommutative

section /- 1E: Small-order groups, normal subgroup of index 2 (pp. 31-34) -/
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Isaacs Thm 1.31: `|G| = p²q` ⇒ Sylow `p` または `q` が正規.

証明方針 (Isaacs §1E):
* `n_q ∣ p²`, `n_q ≡ 1 (mod q)`. 故 `n_q ∈ {1, p, p²}`.
* `n_q = 1`: Sylow `q` 正規.
* `n_q = p`: `q ∣ p − 1`.
* `n_q = p²`: `q ∣ p² − 1 = (p−1)(p+1)`; `q ∣ p−1` または `q ∣ p+1`.
* `q < p` の場合, `q ∣ p − 1` でも `q ∣ p + 1` でも矛盾なく成立し,
  自動的に `n_p = 1` まで進むには別途 `n_p ∣ q`, `n_p ≡ 1 (mod p)` から
  `n_p = 1` を得る (この場合, `q < p` なので `n_p = q` は不可).
* `p < q` の場合, `q ≤ p − 1 < p < q` または `q ≤ p + 1` で `q = p + 1`,
  すなわち `(p, q) = (2, 3)`, `|G| = 12`. このとき `n_3 = 4` から
  `Sylow 2` の正規性を, "元の位数 3 が 8 個, 残り 4 個が Sylow 2" の
  数え上げで示す. -/

/-! ### Thm 1.32 — `|G| = p³q` helpers and main theorem. -/

/-! ### Thm 1.33 — `|G| = 24` で Sylow 2 も Sylow 3 も非正規ならば `G ≅ S₄`. -/

end
end OddOrder.Isaacs.Ch01
end

/-! ### Module `OddOrder.Isaacs.Ch01_Sylow.Main` -/
section
/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# TAIL

Prefix-split from `OddOrder.Isaacs.Ch01_Sylow.Main` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Isaacs.Ch01
open scoped IsMulCommutative

section /- 1E: Small-order groups, normal subgroup of index 2 (pp. 31-34) -/
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Thm 1.36 — `|G| = p^a q` 単純性破壊.  helpers + main. -/

end -- 1E

section /- 1F: Brodkey's theorem on abelian Sylow (pp. 37-38) -/

open Pointwise Subgroup MulAction

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

end -- 1F

section /- 1G: Chermak–Delgado (pp. 41-44) -/

/-! ### §1G (Chermak-Delgado): 本体は別ファイルに分離.

実装本体は [`OddOrder/GroupTheory/ChermakDelgado.lean`](../GroupTheory/ChermakDelgado.lean).

mathlib upstream 視野の shared module 化 (`OddOrder/GroupTheory/` 慣用 dir).
本 section は import + 主要 API への再 export. 詳細実装計画:
[`notes/meta/ch01_chermak_delgado_plan.md`](../../notes/meta/ch01_chermak_delgado_plan.md).

実装一覧 (定理は `Subgroup` namespace 内):

* **Lemma 1.42**: `chermakDelgadoMeasure_le_centralizer`
* **Lemma 1.43**: `chermakDelgadoMeasure_mul_le`
* **Thm 1.44 (a)**: `chermakDelgadoLattice_inf_mem`, `chermakDelgadoLattice_sup_mem`
* **Thm 1.44 (b)**: `chermakDelgadoLattice_sup_eq_mul`
* **Thm 1.44 (c)**: `chermakDelgadoLattice_centralizer_mem`,
  `chermakDelgadoLattice_centralizer_centralizer_eq`
* **Cor 1.45**: `chermakDelgadoSubgroup_mem_lattice`,
  `chermakDelgadoSubgroup_isMulCommutative`, `center_le_chermakDelgadoSubgroup`,
  `chermakDelgadoSubgroup_characteristic`
* **Thm 1.41**: `chermakDelgado` (main theorem)
* **Cor 1.46**: `not_isSimpleGroup_and_nonabelian_of_chermakDelgadoMeasure_gt`

汎用 helper (mathlib upstream 候補): [`OddOrder/Mathlib/Subgroup.lean`](../Mathlib/Subgroup.lean)
の `card_HK_mul_card_inf_eq_card_mul_card`, `le_centralizer_centralizer`, `centralizer_sup` を使用.

関連項目: §1F Brodkey (Thm 1.37-1.40) は Chermak-Delgado から派生する Cor 1.39 の
abelian Sylow 版で, こちらは本ファイル §1F に実装済 (`exists_pair_inf_eq_opCore_of_abelian`,
`index_opCore_le_index_sylow_sq`). -/

export Subgroup (chermakDelgadoMeasure chermakDelgadoLattice chermakDelgadoSubgroup
  chermakDelgadoMeasure_le_centralizer chermakDelgadoMeasure_mul_le
  chermakDelgadoLattice_inf_mem chermakDelgadoLattice_sup_mem
  chermakDelgadoLattice_sup_eq_mul
  chermakDelgadoLattice_centralizer_mem chermakDelgadoLattice_centralizer_centralizer_eq
  chermakDelgadoSubgroup_mem_lattice
  center_le_chermakDelgadoSubgroup chermakDelgado
  not_isSimpleGroup_and_nonabelian_of_chermakDelgadoMeasure_gt)

end -- 1G

end OddOrder.Isaacs.Ch01
end

/-! ### Module `OddOrder.Isaacs.Ch02_Subnormality.Basic` -/
section
/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# Basic

Prefix-split from `OddOrder.Isaacs.Ch02_Subnormality.Main` (2000-line limit, issue 0103 第 2 パス).
-/

open OddOrder.Isaacs.Ch01

/-!
# OddOrder.Isaacs.Ch02 — Subnormality

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 2
"Subnormality" (pp. 45-64) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 2A | 部分正規性の基本・join 定理・Wielandt の F(G) | 2.1 – 2.11 | ✅ 完備 |
| 2B | Baer の定理と Matsuyama の involution 定理 | 2.12 – 2.14 | ✅ 完備 (2.14 = `DihedralBasics.lean`) |
| 2C | p-local 部分群 | 2.15 – 2.17 | ✅ 完備 (`Theorem211Wielandt.lean` / `Main.lean`) |
| 2D | Zenkov と Lucchini | 2.18 – 2.20 | ✅ 完備 (2.20 の本体は `Ch04/ForwardFromCh02.lean`) |

章末演習は `Problems.lean` (§2A + 2B.1) / `ProblemsInvolutions.lean` (§2B の involution 系) /
`ProblemsNGroups.lean` (§2C の N-群) にある。Ch.2 は全ファイル sorry-free。

## 方針

mathlib `Subgroup.IsSubnormal` (inductive predicate + `isSubnormal_iff` chain 表現 +
`subgroupOf` / `inf` / `trans` / `map` / `comap` ら) を全面利用。Ch.1 の `Subgroup.fitting`
(= F(G)) と Thm 1.26 (`Group.isNilpotent_of_finite_tfae` 経由の NormalizerCondition) を
橋渡しに使う。

新規定義は `IsMinimalNormal` (mathlib 未収載). Thm 2.6 や 2.18 で必須。

ノート: [notes/isaacs/ch02_subnormality.md](../../notes/isaacs/ch02_subnormality.md)
-/

namespace OddOrder.Isaacs.Ch02

section /- 2A: Subnormality basics, joins, Wielandt's F(G) (pp. 45-54) -/

/-! ### mathlib 直接利用 (本ファイル内に wrapper を置かない)

CLAUDE.md `## 開発規約 ### mathlib ラッパー方針` に従い, 以下の Isaacs 結果は
mathlib に直接対応があり, 純粋なリネームラッパーは書かない. 呼び出し側で
直接 mathlib 名を使う:

* **Isaacs Cor 2.4** (`S ∩ T subnormal`): `inf_isSubnormal` (本ファイル、2026-08-08 追加)
* (`H ⊴ G ⇒ H ⊴⊴ G`): `Subgroup.Normal.isSubnormal`
* (subnormal の推移律): `Subgroup.IsSubnormal.trans`
* (subnormal の準同型像/逆像/quotient/smul): `.map`, `.comap`, `.quotient`, `.smul`
* (単純群の subnormal は normal): `.normal_of_isSimpleGroup`, `.eq_bot_or_top_of_isSimpleGroup`

下記の wrapper は **適応** または **2 回以上の使用予定** で書く:
* `inf_isSubnormal_subgroupOf` (Thm 2.3): `S ⊓ K |_K = S |_K` への書換を含む
* `commute_of_disjoint_normal` (Lemma 2.7): `Normal` を instance, `M N` を implicit
  に取り直した適応版 (Thm 2.6 等で複数回使う)
-/

variable {G : Type*} [Group G]

/-- **Minimal normal subgroup**: `M` が `G` の非自明正規部分群で、`M` に真に含まれる
`G`-正規部分群は `⊥` のみ。

mathlib 未収載 (`IsAtom` は subgroup lattice 全体に対するもので normal lattice
には対応しない). Isaacs Thm 2.6, 2.18 (Zenkov) で必須。 -/
def IsMinimalNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧ ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥ ∨ N = M

/-- **Isaacs Lemma 2.7**: `M, N ◁ G` で `M ∩ N = 1` ならば `M` の元と `N` の元は可換.

mathlib `Subgroup.commute_of_normal_of_disjoint` の **適応版** —
`Normal` を instance, `M N` を implicit に取り直す (Isaacs 流の呼び出し記法).
Thm 2.6 等で複数回使用予定. (CLAUDE.md mathlib ラッパー方針の例外規定に該当.) -/
theorem commute_of_disjoint_normal {M N : Subgroup G} [hM : M.Normal] [hN : N.Normal]
    (hDis : Disjoint M N) {m n : G} (hm : m ∈ M) (hn : n ∈ N) : Commute m n :=
  Subgroup.commute_of_normal_of_disjoint M N hM hN hDis m n hm hn

/-! ### Socle (全 minimal normal subgroup の sup), Thm 2.6 への準備 -/

variable (G) in
/-- **Socle**: `G` の全ての minimal normal subgroup の sup.

`Soc(G)` (Isaacs では §4Aで導入, p.92). Thm 2.6 で `M ≤ Soc(N)` の経路を作るのに使う.
mathlib 未収載. -/
def socle : Subgroup G :=
  ⨆ M : {M : Subgroup G // IsMinimalNormal M}, (M : Subgroup G)

/-- minimal normal subgroup は socle に含まれる. (`le_iSup` 適応; 章内で 2 回以上使う.) -/
theorem isMinimalNormal_le_socle {M : Subgroup G} (hM : IsMinimalNormal M) :
    M ≤ socle G :=
  le_iSup (fun M : {M : Subgroup G // IsMinimalNormal M} => (M : Subgroup G)) ⟨M, hM⟩

/-- `Soc(G)` は `G` の正規部分群. 各 minimal normal の正規性を `iSup_induction` で
全体に持ち上げる. テンプレートは [`Ch01_Sylow/Main.lean` `fitting.normal`](Ch01_Sylow/Main.lean#L834). -/
instance socle.normal : (socle G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ socle G) hn
    ?mem ?one ?mul
  case mem =>
    rintro ⟨M, hM⟩ x hx
    exact isMinimalNormal_le_socle hM (hM.1.conj_mem x hx g)
  case one => simp
  case mul =>
    intro x y hx hy
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (socle G).mul_mem hx hy

/-- minimal normal subgroup は MulEquiv `ϕ : G ≃* G` による像も minimal normal. -/
theorem IsMinimalNormal.map_equiv {M : Subgroup G} (hM : IsMinimalNormal M) (ϕ : G ≃* G) :
    IsMinimalNormal (M.map ϕ.toMonoidHom) := by
  refine ⟨hM.1.map ϕ.toMonoidHom ϕ.surjective, ?_, ?_⟩
  · -- `M.map ϕ ≠ ⊥` since `ϕ` injective ⇒ image of a nontrivial subgroup is nontrivial.
    intro heq
    apply hM.2.1
    rw [eq_bot_iff]
    intro m hm
    have hmem : ϕ m ∈ M.map ϕ.toMonoidHom := ⟨m, hm, rfl⟩
    rw [heq, Subgroup.mem_bot] at hmem
    have h1 : m = 1 := ϕ.injective (by rw [hmem]; exact (ϕ.map_one).symm)
    rw [h1]; exact Subgroup.one_mem _
  · -- minimality: any `N ≤ M.map ϕ` normal in `G` must be `⊥` or `M.map ϕ`.
    intro N hN hNle
    -- Move along ϕ.symm.
    have hN' : (N.map ϕ.symm.toMonoidHom).Normal := hN.map ϕ.symm.toMonoidHom ϕ.symm.surjective
    have hle : N.map ϕ.symm.toMonoidHom ≤ M := by
      rintro _ ⟨y, hyN, rfl⟩
      rcases hNle hyN with ⟨z, hzM, hzeq⟩
      have h1 : ϕ.symm.toMonoidHom y = z := by
        change ϕ.symm y = z
        rw [← hzeq]; exact ϕ.symm_apply_apply z
      rw [h1]; exact hzM
    -- Transport back: N = (N.map ϕ.symm).map ϕ via map_map and ϕ.symm.trans ϕ = id.
    have hback : (N.map ϕ.symm.toMonoidHom).map ϕ.toMonoidHom = N := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id N
      ext x; simp
    rcases hM.2.2 _ hN' hle with hbot | htop
    · left
      rw [← hback, hbot, Subgroup.map_bot]
    · right
      rw [← hback, htop]

/-- `Soc(G)` は `G` の特性部分群. 任意の `ϕ : G ≃* G` について `(Soc G).map ϕ ≤ Soc G`
を `characteristic_iff_map_le` で示す. -/
instance socle.characteristic : (socle G).Characteristic := by
  refine (Subgroup.characteristic_iff_map_le).mpr ?_
  intro ϕ
  change (⨆ M : {M : Subgroup G // IsMinimalNormal M}, (M : Subgroup G)).map
      ϕ.toMonoidHom ≤ socle G
  rw [Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨M, hM⟩
  exact isMinimalNormal_le_socle (hM.map_equiv ϕ)

/-- 有限群の任意の非自明な正規部分群は minimal normal subgroup を含む.
`Nat.card N` の強induction. テンプレートは `isSubnormal_of_isNilpotent_finite`. -/
theorem exists_isMinimalNormal_le_of_normal [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N := by
  classical
  -- We need to carry `N.Normal` through the induction; promote it to an explicit hyp.
  suffices h : ∀ (k : ℕ) (N : Subgroup G), N.Normal → Nat.card N ≤ k → N ≠ ⊥ →
      ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N by
    exact h (Nat.card N) N ‹N.Normal› le_rfl hN
  intro k
  induction k with
  | zero =>
    intro N _ hcard _
    -- Nat.card N = 0 contradiction with Nat.card_pos
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ k ih =>
    intro N hNn hcard hNne
    by_cases hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N
    · exact ⟨N, ⟨hNn, hNne, hmin⟩, le_rfl⟩
    · push Not at hmin
      obtain ⟨K, hKnorm, hKleN, hKne_bot, hKne_N⟩ := hmin
      have hKlt : K < N := lt_of_le_of_ne hKleN hKne_N
      have hsub : (K : Set G) ⊂ (N : Set G) := SetLike.coe_ssubset_coe.mpr hKlt
      obtain ⟨x, hxN, hxK⟩ := Set.exists_of_ssubset hsub
      have hcard_K : Nat.card K < Nat.card N := by
        have hequiv : K ≃ {n : N // (n : G) ∈ K} :=
          { toFun := fun ⟨g, hg⟩ => ⟨⟨g, hKleN hg⟩, hg⟩
            invFun := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, hg⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
        rw [Nat.card_congr hequiv]
        exact Finite.card_subtype_lt (p := fun n : N => (n : G) ∈ K)
          (x := ⟨x, hxN⟩) hxK
      have hcard_K_le : Nat.card K ≤ k := by omega
      obtain ⟨M, hMmin, hMleK⟩ := ih K hKnorm hcard_K_le hKne_bot
      exact ⟨M, hMmin, hMleK.trans hKleN⟩

/-! ### Isaacs Thm 2.2 (`H ⊆ F(G) ⇔ H` 冪零 + subnormal) -/

/-- 補助補題 (Thm 2.6 の strong induction の generalized core).

`n : ℕ` についての induction で, 任意の有限群 `G` (with `|G| ≤ n`) に対し,
任意の subnormal `S` と minimal normal `M` で `M ≤ N_G(S)` を示す. -/
private theorem isMinimalNormal_le_normalizer_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {S M : Subgroup G}, S.IsSubnormal → IsMinimalNormal M →
      M ≤ Subgroup.normalizer (S : Set G) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _ _
    -- Nat.card G = 0 contradicts the fact that G has the identity.
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ hG S M hS hM
    classical
    have _ : M.Normal := hM.1
    by_cases hStop : S = ⊤
    · -- normalizer of ⊤ is ⊤ (since ⊤ is normal).
      subst hStop
      rw [Subgroup.normalizer_eq_top (⊤ : Subgroup G)]
      exact le_top
    · obtain ⟨N, hNnorm, hSleN, hNlt⟩ := hS.exists_normal_and_le_and_lt_top_of_ne hStop
      have _ := hNnorm
      by_cases hMN : M ⊓ N = ⊥
      · -- Case 1: M ⊓ N = ⊥. M and N commute; S ≤ N ⇒ M centralizes S.
        intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · intro hsS
          have hsN : s ∈ N := hSleN hsS
          have hcomm : Commute m s := commute_of_disjoint_normal
            (M := M) (N := N) (disjoint_iff.mpr hMN) hm hsN
          have hmsm : m * s * m⁻¹ = s := by
            rw [Commute.eq hcomm, mul_inv_cancel_right]
          rw [hmsm]; exact hsS
        · intro hmsm
          have hsN : m * s * m⁻¹ ∈ N := hSleN hmsm
          have hm_inv : m⁻¹ ∈ M := M.inv_mem hm
          have hcomm : Commute m⁻¹ (m * s * m⁻¹) := commute_of_disjoint_normal
            (M := M) (N := N) (disjoint_iff.mpr hMN) hm_inv hsN
          have hseq : s = m⁻¹ * (m * s * m⁻¹) * m := by group
          rw [hseq, Commute.eq hcomm, mul_assoc, inv_mul_cancel, mul_one]
          exact hmsm
      · -- Case 2: M ⊓ N ≠ ⊥. By minimality of M, M ⊓ N = M, i.e., M ≤ N.
        have hMN_le_M : M ⊓ N ≤ M := inf_le_left
        have hMN_norm : (M ⊓ N).Normal := Subgroup.normal_inf_normal M N
        have hMN_eq_M : M ⊓ N = M := by
          rcases hM.2.2 (M ⊓ N) hMN_norm hMN_le_M with h | h
          · exact absurd h hMN
          · exact h
        have hMleN : M ≤ N := by
          have h : M ≤ M ⊓ N := le_of_eq hMN_eq_M.symm
          exact (le_inf_iff.mp h).2
        -- |N| < |G| ≤ n+1 so |N| ≤ n.
        have hN_ne_top : N ≠ ⊤ := hNlt.ne
        obtain ⟨g, hg⟩ : ∃ g : G, g ∉ N := by
          by_contra h
          push Not at h
          exact hN_ne_top (eq_top_iff.mpr fun x _ => h x)
        have hN_card_lt : Nat.card N < Nat.card G :=
          Finite.card_subtype_lt (p := fun x : G => x ∈ N) (x := g) hg
        have hN_card_le_n : Nat.card N ≤ n := by omega
        have hNne_bot : N ≠ ⊥ := by
          intro h
          apply hM.2.1
          rw [eq_bot_iff]; rw [h] at hMleN; exact hMleN
        have hNNontriv : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne_bot
        -- IH on ↥N.
        have hSsubN_sn : (S.subgroupOf N).IsSubnormal := hS.subgroupOf
        have hIH : ∀ K : Subgroup N, IsMinimalNormal K →
            K ≤ Subgroup.normalizer (S.subgroupOf N : Set N) := by
          intro K hK
          exact ih N hN_card_le_n hSsubN_sn hK
        have hSoc_le_norm_inner : socle N ≤ Subgroup.normalizer (S.subgroupOf N : Set N) := by
          refine iSup_le ?_
          rintro ⟨K, hK⟩
          exact hIH K hK
        -- Lift: (socle N).map N.subtype ≤ normalizer S in G.
        have hSoc_lift_le_norm :
            (socle N).map N.subtype ≤ Subgroup.normalizer (S : Set G) := by
          rintro _ ⟨⟨g', hg'N⟩, hg'soc, rfl⟩
          change (g' : G) ∈ Subgroup.normalizer (S : Set G)
          have hg'norm : (⟨g', hg'N⟩ : N) ∈
              Subgroup.normalizer (S.subgroupOf N : Set N) := hSoc_le_norm_inner hg'soc
          rw [Subgroup.mem_normalizer_iff] at hg'norm ⊢
          intro s
          by_cases hsN : s ∈ N
          · -- s ∈ N: lift to N, apply hg'norm.
            have hpair := hg'norm ⟨s, hsN⟩
            constructor
            · intro hsS
              have h1 : (⟨s, hsN⟩ : N) ∈ S.subgroupOf N := by
                rwa [Subgroup.mem_subgroupOf]
              have h2 := hpair.mp h1
              rw [Subgroup.mem_subgroupOf] at h2
              -- h2 : ((⟨g', _⟩ * ⟨s, _⟩ * ⟨g', _⟩⁻¹ : N) : G) ∈ S
              -- coerce: (⟨a, _⟩ * ⟨b, _⟩ : N : G) = a * b in G.
              simpa using h2
            · intro hgsg
              have hgsg_N : g' * s * g'⁻¹ ∈ N := hNnorm.conj_mem s hsN g'
              have h1 : (⟨g' * s * g'⁻¹, hgsg_N⟩ : N) ∈ S.subgroupOf N := by
                rwa [Subgroup.mem_subgroupOf]
              -- Identify ⟨g' * s * g'⁻¹, _⟩ with ⟨g', _⟩ * ⟨s, _⟩ * ⟨g', _⟩⁻¹ as N-element.
              have hcong : (⟨g' * s * g'⁻¹, hgsg_N⟩ : N) =
                  ⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ := by
                apply Subtype.ext
                change g' * s * g'⁻¹ = (↑(⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ : N) : G)
                push_cast
                rfl
              rw [hcong] at h1
              have h2 := hpair.mpr h1
              rwa [Subgroup.mem_subgroupOf] at h2
          · -- s ∉ N: both sides false.
            have hgsg_notN : g' * s * g'⁻¹ ∉ N := by
              intro h
              apply hsN
              have hseq : s = g'⁻¹ * (g' * s * g'⁻¹) * g' := by group
              rw [hseq]
              have h' : g'⁻¹ * (g' * s * g'⁻¹) * (g'⁻¹)⁻¹ ∈ N :=
                hNnorm.conj_mem _ h g'⁻¹
              rwa [inv_inv] at h'
            constructor
            · intro hsS; exact absurd (hSleN hsS) hsN
            · intro hgsg; exact absurd (hSleN hgsg) hgsg_notN
        -- M.subgroupOf N is normal in N (since M is normal in G and M ≤ N).
        have hMsubN_norm : (M.subgroupOf N).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hMleN).mpr
            Subgroup.le_normalizer_of_normal
        -- M.subgroupOf N ≠ ⊥ (since M ≠ ⊥ and M ≤ N).
        have hMsubN_ne_bot : M.subgroupOf N ≠ ⊥ := by
          intro heq
          apply hM.2.1
          have hM_eq : M = (M.subgroupOf N).map N.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hMleN).symm
          rw [hM_eq, heq, Subgroup.map_bot]
        -- Pick a minimal-normal-in-N subgroup K ≤ M.subgroupOf N.
        obtain ⟨K, hKmin, hKle⟩ :=
          exists_isMinimalNormal_le_of_normal (G := N) (M.subgroupOf N) hMsubN_ne_bot
        have hK_le_socN : K ≤ socle N := isMinimalNormal_le_socle hKmin
        -- K.map N.subtype ≤ M ∩ (socle N).map N.subtype, and ≠ ⊥.
        have hKmap_le_M : K.map N.subtype ≤ M := by
          rintro _ ⟨k, hk, rfl⟩
          have := hKle hk
          rwa [Subgroup.mem_subgroupOf] at this
        have hKmap_le_socMap : K.map N.subtype ≤ (socle N).map N.subtype :=
          Subgroup.map_mono hK_le_socN
        have hKmap_ne_bot : K.map N.subtype ≠ ⊥ := by
          intro heq
          apply hKmin.2.1
          rw [eq_bot_iff]
          intro k hk
          have hmem : (k : G) ∈ K.map N.subtype := ⟨k, hk, rfl⟩
          rw [heq, Subgroup.mem_bot] at hmem
          have : k = 1 := Subtype.ext hmem
          rw [this]; exact Subgroup.one_mem _
        -- M ⊓ ((socle N).map N.subtype) is G-normal, ≤ M, ≠ ⊥.
        have hSocLift_normal : ((socle N).map N.subtype).Normal := inferInstance
        have hM_inf_norm : (M ⊓ (socle N).map N.subtype).Normal :=
          Subgroup.normal_inf_normal _ _
        have hM_inf_ne_bot : M ⊓ (socle N).map N.subtype ≠ ⊥ := by
          intro heq
          apply hKmap_ne_bot
          rw [eq_bot_iff]
          exact (le_inf hKmap_le_M hKmap_le_socMap).trans heq.le
        have hM_inf_eq_M : M ⊓ (socle N).map N.subtype = M := by
          rcases hM.2.2 _ hM_inf_norm inf_le_left with h | h
          · exact absurd h hM_inf_ne_bot
          · exact h
        have hM_le_SocLift : M ≤ (socle N).map N.subtype := by
          intro m hm
          have hmem : m ∈ M ⊓ (socle N).map N.subtype := by rw [hM_inf_eq_M]; exact hm
          exact hmem.2
        exact hM_le_SocLift.trans hSoc_lift_le_norm

/-- **Isaacs Thm 2.6** (minimal normal が subnormal を正規化).

Subnormal `S ⊴⊴ G` と minimal normal `M` について `M ≤ N_G(S)`.

Isaacs p.46 の証明: `|G|`-induction.
* `S = ⊤` なら `N_G(⊤) = ⊤` で trivial.
* `S ≠ ⊤` なら proper G-正規 `N` で `S ≤ N` を取る.
  - **Case 1** `M ⊓ N = ⊥`: `commute_of_disjoint_normal` で `M` と `N` の元は可換,
    特に `S ≤ N` の元とも可換 ⇒ `M ≤ centralizer S ≤ normalizer S`.
  - **Case 2** `M ⊓ N ≠ ⊥`: minimality で `M ≤ N`. IH を ambient group `↥N` に適用し,
    `socle ↥N` の各 minimal normal が `S.subgroupOf N` を正規化 ⇒ `S` を正規化.
    Characteristic 経由で `(socle ↥N).map N.subtype` は `G` 正規, `M ≤ ↥N` と合わせ
    minimality 適用. -/
theorem isMinimalNormal_le_normalizer_of_isSubnormal [Finite G]
    {S M : Subgroup G} (hS : S.IsSubnormal) (hM : IsMinimalNormal M) :
    M ≤ Subgroup.normalizer (S : Set G) :=
  isMinimalNormal_le_normalizer_aux (Nat.card G) G le_rfl hS hM

/-! ### Isaacs Thm 2.8 (permutability ⇒ subnormality) -/

end
end OddOrder.Isaacs.Ch02
end

/-! ### Module `OddOrder.Isaacs.Ch09_MoreSubnormality.Semisimple` -/
section
/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# Isaacs Ch. 9 — §9A: semisimple groups と Lemma 9.5 / Lemma 9.6 (pp. 274-275)

- `IsSemisimpleGroup`: **semisimple** = nonabelian simple normal subgroups の積 (書籍 p. 274).
- **Lemma 9.5** (分割して形式化):
  - `isMinimalNormal_of_mem_semisimpleFamily`: 族の各メンバーは minimal normal.
  - `iSupIndep_of_semisimpleFamily` + `piEquivOfSemisimpleFamily`: 積は直積
    (mathlib `MonoidHom.noncommPiCoprod` による `(Π S, ↥S) ≃* G`).
  - `center_eq_bot_of_semisimpleFamily`: semisimple 群は centerless.
  - `mem_semisimpleFamily_of_isMinimalNormal`: 族は `G` の全 minimal normal subgroup と一致.
- **Lemma 9.6** (`isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal`):
  有限群の minimal normal subgroup は abelian か semisimple.
- 下流 (Thm 9.7/9.8) 向け payload:
  - `IsSemisimpleGroup.isSimpleGroup_of_isMinimalNormal`: semisimple 群の minimal normal は
    nonabelian simple.
  - `IsSemisimpleGroup.eq_bot_of_normal_of_isSolvable`: semisimple 群の solvable normal
    subgroup は自明 (Thm 9.7(c) の核心ステップ).

`normal_map_subtype_of_char` は「characteristic in normal ⇒ ambient で normal」の局所
private copy (同じ補題が `BG.Ch3.S10` と Ch10 `TransferIndexPrime` にもあり、shared 化は
issue 9109; BG 版と `GroupTheory` 版の同名 public 化は Huppert.lean の無修飾参照と衝突する
ため一本化は所有レーン込みの調整タスクとして繰延)。

Lemma 9.6 の実装ノート: 書籍は `N` の minimal normal `S` を `↥N` の中で取るが、
subgroup-of-subgroup の輸送を避けるため `S₀ := S.map N.subtype : Subgroup G` に押し出して
**すべて `G` レベルで**議論する。abelian 枝は `F(N)`, `Z(N)` の押し出し
(`normal_map_subtype_of_char`, issue 9109) が `G`-normal で `N` の
minimality に食われることから `N` 可換を得る。nonabelian 枝は `S₀` の simple 性を
`Subgroup.isSimpleGroup_iff` + Thm 2.6 (subnormal 鎖 `K₀ ⊴ S₀ ⊴ N ⊴ G`) で示し、
`G`-共役族 `{S₀ᵍ}` の join が `G`-normal になって `N` と一致 → `↥N` の semisimple 族を成す.

`center_eq_bot` 系は直積構造 (`noncommPiCoprod` の単射性・全射性) を経由するため
`[Finite G]` を仮定する (Isaacs は有限群の本; 族の有限性が本質).
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

section /- 9A: semisimple groups (pp. 274-275) -/

variable {G : Type*} [Group G]

/-- 相異なる minimal normal subgroups は交わらない. -/
theorem disjoint_of_isMinimalNormal_of_ne {M N : Subgroup G}
    (hM : Ch02.IsMinimalNormal M) (hN : Ch02.IsMinimalNormal N) (hne : M ≠ N) :
    Disjoint M N := by
  have := hM.1
  have := hN.1
  rw [disjoint_iff]
  rcases hM.2.2 (M ⊓ N) (Subgroup.normal_inf_normal M N) inf_le_left with h | h
  · exact h
  · -- M ⊓ N = M ⇒ M ≤ N ⇒ (minimality of N) M = N, 矛盾
    have hMN : M ≤ N := h ▸ inf_le_right
    rcases hN.2.2 M hM.1 hMN with hbot | heq
    · exact absurd hbot hM.2.1
    · exact absurd heq hne

/-- **Semisimple group** (Isaacs p. 274): nonabelian simple normal subgroups の
族の積 (`sSup`) が全体. -/
def IsSemisimpleGroup (G : Type*) [Group G] : Prop :=
  ∃ 𝒳 : Set (Subgroup G),
    (∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S) ∧ sSup 𝒳 = ⊤

variable {𝒳 : Set (Subgroup G)}

/-- **Isaacs Lemma 9.5 (前半)**: nonabelian simple normal subgroup は minimal normal.
(`G`-normal な部分群は `↥S` でも normal で, simple 性から `⊥` か `S`.) -/
theorem isMinimalNormal_of_mem_semisimpleFamily
    (h𝒳 : ∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S)
    {S : Subgroup G} (hS : S ∈ 𝒳) : Ch02.IsMinimalNormal S := by
  obtain ⟨hnormal, hsimple, -⟩ := h𝒳 S hS
  obtain ⟨hne_bot, hmin⟩ := Subgroup.isSimpleGroup_iff.mp hsimple
  exact ⟨hnormal, hne_bot, fun K hK hKle => hmin K hKle (hK.subgroupOf S)⟩

/-- 族の相異なるメンバーの元は可換 (Lemma 9.5 第 1 段落). -/
theorem commute_of_mem_semisimpleFamily_of_ne
    (h𝒳 : ∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S)
    {S T : Subgroup G} (hS : S ∈ 𝒳) (hT : T ∈ 𝒳) (hne : S ≠ T)
    {x y : G} (hx : x ∈ S) (hy : y ∈ T) : Commute x y :=
  Subgroup.commute_of_normal_of_disjoint S T (h𝒳 S hS).1 (h𝒳 T hT).1
    (disjoint_of_isMinimalNormal_of_ne (isMinimalNormal_of_mem_semisimpleFamily h𝒳 hS)
      (isMinimalNormal_of_mem_semisimpleFamily h𝒳 hT) hne) x y hx hy

end

section /- 9A: Lemma 9.6 (p. 275) -/

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- `N ⊴ W` の characteristic subgroup `L ≤ ↥N` の ambient 押し出しは `W` で正規.
「characteristic in normal ⇒ normal」の局所版 (shared 化は issue 9109). -/
private theorem normal_map_subtype_of_char {W : Type*} [Group W] {N : Subgroup W}
    [N.Normal] {L : Subgroup ↥N} (hL : L.Characteristic) :
    (L.map N.subtype).Normal := by
  refine ⟨fun a ha w => ?_⟩
  obtain ⟨⟨a', ha'N⟩, ha'L, rfl⟩ := ha
  have hmap : L.map (MulAut.conjNormal w).toMonoidHom = L :=
    (Subgroup.characteristic_iff_map_eq.mp hL) (MulAut.conjNormal w)
  have hmem : (MulAut.conjNormal w) ⟨a', ha'N⟩ ∈ L := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ ha'L
  exact ⟨(MulAut.conjNormal w) ⟨a', ha'N⟩, hmem, MulAut.conjNormal_apply w ⟨a', ha'N⟩⟩

/-- **Isaacs Lemma 9.6**: 有限群の minimal normal subgroup は abelian か semisimple.

`↥N` の minimal normal `S` を `G` へ押し出した `S₀` で場合分け:
abelian なら `F(N)`, `Z(N)` の押し出しが `G`-normal (issue 9109 の
`normal_map_subtype_of_char`) となり `N` の minimality から
`N` は可換. nonabelian なら Thm 2.6 の subnormal 鎖で `S₀` が simple になり,
`G`-共役族の join が `N` に一致して semisimple 族を成す. -/
theorem isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal [Finite G]
    {N : Subgroup G} (hN : Ch02.IsMinimalNormal N) :
    IsMulCommutative ↥N ∨ IsSemisimpleGroup ↥N := by
  have := hN.1
  have hNnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  have htop_ne : (⊤ : Subgroup ↥N) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥N)
    exact hx (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top x))
  obtain ⟨S, hSmin, -⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup ↥N) htop_ne
  set S₀ : Subgroup G := S.map N.subtype with hS₀def
  have hS₀le : S₀ ≤ N := Subgroup.map_subtype_le S
  have hS₀recover : S₀.subgroupOf N = S :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective S
  have hS₀ne : S₀ ≠ ⊥ := by
    intro h
    apply hSmin.2.1
    rw [← hS₀recover, h, Subgroup.bot_subgroupOf]
  have hS₀normalN : (S₀.subgroupOf N).Normal := hS₀recover ▸ hSmin.1
  by_cases habel : IsMulCommutative ↥S₀
  · -- abelian 枝: `N` は可換
    left
    have : IsMulCommutative ↥(S₀.subgroupOf N) := by
      have := habel
      exact isMulCommutative_of_surjective
        (Subgroup.subgroupOfEquivOfLe hS₀le).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hS₀le).symm.surjective
    have := hS₀normalN
    have hfit : S₀.subgroupOf N ≤ Ch01.fitting ↥N := Ch01.nilpotent_normal_le_fitting
    have hFnormal : ((Ch01.fitting ↥N).map N.subtype).Normal :=
      normal_map_subtype_of_char (Ch01.fitting.characteristic ↥N)
    have hFne : (Ch01.fitting ↥N).map N.subtype ≠ ⊥ := by
      intro h
      rw [Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at h
      exact hSmin.2.1 (by rw [← hS₀recover]; exact le_bot_iff.mp (h ▸ hfit))
    rcases hN.2.2 _ hFnormal (Subgroup.map_subtype_le _) with h | h
    · exact absurd h hFne
    have hfit_top : Ch01.fitting ↥N = ⊤ := by
      apply Subgroup.map_injective N.subtype_injective
      rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have : Group.IsNilpotent ↥N := by
      have h1 : Group.IsNilpotent ↥(⊤ : Subgroup ↥N) :=
        hfit_top ▸ Ch01.fitting.isNilpotent (G := ↥N)
      exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv
    have hZnormal : ((center ↥N).map N.subtype).Normal :=
      normal_map_subtype_of_char Subgroup.centerCharacteristic
    have hZne : (center ↥N).map N.subtype ≠ ⊥ := by
      intro h
      rw [Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at h
      exact Group.IsNilpotent.center_ne_bot (G := ↥N) h
    rcases hN.2.2 _ hZnormal (Subgroup.map_subtype_le _) with h | h
    · exact absurd h hZne
    have hcenter_top : center ↥N = ⊤ := by
      apply Subgroup.map_injective N.subtype_injective
      rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact IsMulCommutative.of_comm fun a b =>
      Subgroup.mem_center_iff.mp (hcenter_top ▸ Subgroup.mem_top b) a
  · -- nonabelian 枝: `N` は semisimple
    right
    -- Step 1: `S₀` は simple (Thm 2.6 の subnormal 鎖で `K₀ ⊴ N` に格上げ)
    have hS₀simple : IsSimpleGroup ↥S₀ := by
      rw [Subgroup.isSimpleGroup_iff]
      refine ⟨hS₀ne, fun K₀ hK₀le hK₀norm => ?_⟩
      by_cases hbot : K₀ = ⊥
      · exact Or.inl hbot
      refine Or.inr ?_
      have hK₀N : K₀ ≤ N := hK₀le.trans hS₀le
      have hK₀sub : K₀.IsSubnormal := by
        have hS₀sub : S₀.IsSubnormal :=
          Subgroup.IsSubnormal.trans hS₀le hS₀normalN.isSubnormal hN.1.isSubnormal
        exact Subgroup.IsSubnormal.trans hK₀le hK₀norm.isSubnormal hS₀sub
      have hK₀normalN : (K₀.subgroupOf N).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀N).mpr
          (Ch02.isMinimalNormal_le_normalizer_of_isSubnormal hK₀sub hN)
      have hle' : K₀.subgroupOf N ≤ S := by
        rw [← hS₀recover]
        exact fun x hx => hK₀le hx
      rcases hSmin.2.2 _ hK₀normalN hle' with h | h
      · exfalso
        apply hbot
        have hmap := congrArg (Subgroup.map N.subtype) h
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK₀N, Subgroup.map_bot] at hmap
      · have hmap := congrArg (Subgroup.map N.subtype) h
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK₀N, ← hS₀def] at hmap
    -- Step 2: `G`-共役族とその join `T`
    have hconj_le : ∀ g : G, S₀.map (MulAut.conj g).toMonoidHom ≤ N := by
      rintro g x ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply] using hN.1.conj_mem s (hS₀le hs) g
    have hcomp : ∀ h g : G,
        (S₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom
          = S₀.map (MulAut.conj (h * g)).toMonoidHom := by
      intro h g
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    set T : Subgroup G := ⨆ g : G, S₀.map (MulAut.conj g).toMonoidHom with hTdef
    have hS₀T : S₀ ≤ T := by
      refine le_trans (le_of_eq ?_) (le_iSup (fun g : G => S₀.map (MulAut.conj g).toMonoidHom) 1)
      ext x
      simp [Subgroup.mem_map]
    have hperm : ∀ h : G, T.map (MulAut.conj h).toMonoidHom = T := by
      intro h
      rw [hTdef, Subgroup.map_iSup]
      refine le_antisymm (iSup_le fun g => ?_) (iSup_le fun g => ?_)
      · rw [hcomp h g]
        exact le_iSup (fun g' : G => S₀.map (MulAut.conj g').toMonoidHom) (h * g)
      · refine le_trans (le_of_eq ?_) (le_iSup (fun g' : G =>
          (S₀.map (MulAut.conj g').toMonoidHom).map (MulAut.conj h).toMonoidHom) (h⁻¹ * g))
        rw [hcomp h (h⁻¹ * g), mul_inv_cancel_left]
    have hTnormal : T.Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hmem : (MulAut.conj g).toMonoidHom x ∈ T.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hperm g] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hTN : T = N := by
      rcases hN.2.2 T hTnormal (iSup_le hconj_le : T ≤ N) with h | h
      · exact absurd h fun hb => hS₀ne (le_bot_iff.mp (hb ▸ hS₀T))
      · exact h
    -- Step 3: 共役は `↥N` の normal subgroup
    have haux : ∀ g : G, ∀ n ∈ N, ∀ x ∈ S₀.map (MulAut.conj g).toMonoidHom,
        n * x * n⁻¹ ∈ S₀.map (MulAut.conj g).toMonoidHom := by
      have hNnorm : N ≤ Subgroup.normalizer (S₀ : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hS₀le).mp hS₀normalN
      rintro g n hn x ⟨s, hs, rfl⟩
      have hm : g⁻¹ * n * g ∈ N := by simpa using hN.1.conj_mem n hn g⁻¹
      have hs' : (g⁻¹ * n * g) * s * (g⁻¹ * n * g)⁻¹ ∈ S₀ :=
        (Subgroup.mem_normalizer_iff.mp (hNnorm hm) s).mp hs
      refine ⟨(g⁻¹ * n * g) * s * (g⁻¹ * n * g)⁻¹, hs', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hnorm_conj : ∀ g : G,
        ((S₀.map (MulAut.conj g).toMonoidHom).subgroupOf N).Normal := by
      intro g
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hconj_le g)]
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => haux g n hn x hx, fun hx => ?_⟩
      have hback := haux g n⁻¹ (inv_mem hn) _ hx
      have heq : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
      rwa [heq] at hback
    -- Step 4: semisimple 族の組み立て
    refine ⟨Set.range (fun g : G =>
      (S₀.map (MulAut.conj g).toMonoidHom).subgroupOf N), ?_, ?_⟩
    · rintro P ⟨g, rfl⟩
      have := hS₀simple
      have e : ↥((S₀.map (MulAut.conj g).toMonoidHom).subgroupOf N) ≃* ↥S₀ :=
        (Subgroup.subgroupOfEquivOfLe (hconj_le g)).trans
          (Subgroup.equivMapOfInjective S₀ (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective).symm
      refine ⟨hnorm_conj g, e.isSimpleGroup, fun hcomm => habel ?_⟩
      have := hcomm
      exact isMulCommutative_of_surjective e.toMonoidHom e.surjective
    · apply Subgroup.map_injective N.subtype_injective
      rw [sSup_range, Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hmapg : ∀ g : G,
          ((S₀.map (MulAut.conj g).toMonoidHom).subgroupOf N).map N.subtype
            = S₀.map (MulAut.conj g).toMonoidHom := by
        intro g
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hconj_le g)]
      simp_rw [hmapg]
      exact hTN

end

end OddOrder.Isaacs.Ch09
end

/-! ### Module `SocleReduction` -/
section
/-
Copyright (c) 2026 Contributors to the Conjecture 5.5 formalization.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! The elementary almost-simple reduction after the external input that
nonabelian finite simple groups have order divisible by four. -/

namespace Conjecture55Socle
open Subgroup OddOrder.Isaacs
open scoped IsMulCommutative
universe u

/-- Two disjoint commuting subgroups of orders divisible by four force
sixteen to divide the ambient group order. -/
theorem sixteen_dvd_of_disjoint_commuting
    {G : Type*} [Group G] [Finite G] (S T : Subgroup G)
    (hd : Disjoint S T)
    (hc : ∀ (s : S) (t : T), Commute (s : G) (t : G))
    (hS : 4 ∣ Nat.card S) (hT : 4 ∣ Nat.card T) : 16 ∣ Nat.card G := by
  let f : S × T →* G := S.subtype.noncommCoprod T.subtype hc
  have hf : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    exact ⟨S.subtype_injective, T.subtype_injective, by simpa using hd⟩
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_prod] at hdvd
  exact (show 16 ∣ Nat.card S * Nat.card T from mul_dvd_mul hS hT).trans hdvd

/-- A nontrivial semisimple group whose order is not divisible by sixteen
has only one simple factor, provided each factor has order divisible by four. -/
theorem simple_of_semisimple_of_not_sixteen_dvd
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hss : Ch09.IsSemisimpleGroup G) (h16 : ¬16 ∣ Nat.card G)
    (hfour : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H → 4 ∣ Nat.card H) :
    IsSimpleGroup G ∧ ¬IsMulCommutative G := by
  classical
  obtain ⟨X, hX, hsup⟩ := hss
  have hne : X.Nonempty := by
    by_contra h
    have he : X = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, sSup_empty] at hsup
    exact bot_ne_top hsup
  obtain ⟨S, hS⟩ := hne
  have hu : ∀ T ∈ X, T = S := by
    intro T hT
    by_contra hTS
    apply h16
    apply sixteen_dvd_of_disjoint_commuting T S
    · exact Ch09.disjoint_of_isMinimalNormal_of_ne
        (Ch09.isMinimalNormal_of_mem_semisimpleFamily hX hT)
        (Ch09.isMinimalNormal_of_mem_semisimpleFamily hX hS) hTS
    · intro t s
      exact Ch09.commute_of_mem_semisimpleFamily_of_ne hX hT hS hTS t.2 s.2
    · exact hfour T (hX T hT).2.1 (hX T hT).2.2
    · exact hfour S (hX S hS).2.1 (hX S hS).2.2
  have hXS : X = {S} := Set.eq_singleton_iff_unique_mem.mpr ⟨hS, hu⟩
  have hStop : S = ⊤ := by simpa [hXS] using hsup
  let e : S ≃* G := (MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv
  have : IsSimpleGroup S := (hX S hS).2.1
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  intro hcomm
  let : IsMulCommutative G := hcomm
  exact (hX S hS).2.2
    (Ch09.isMulCommutative_of_surjective e.symm.toMonoidHom e.symm.surjective)

/-- Under the simple-group order input, every minimal normal subgroup of a
radical-free group with no sixteen in its order is nonabelian simple. -/
theorem minimal_normal_isSimple_of_radicalFree
    {G : Type u} [Group G] [Finite G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h16 : ¬16 ∣ Nat.card G)
    (hfour : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H → 4 ∣ Nat.card H)
    {N : Subgroup G} (hN : Ch02.IsMinimalNormal N) :
    IsSimpleGroup N ∧ ¬IsMulCommutative N := by
  have hnc : ¬IsMulCommutative N := by
    intro hcomm
    let : IsMulCommutative N := hcomm
    exact hN.2.1 (hrad N hN.1 inferInstance)
  have hss := (Ch09.isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hN).resolve_left hnc
  have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN.2.1
  exact simple_of_semisimple_of_not_sixteen_dvd hss
    (fun h => h16 (h.trans N.card_subgroup_dvd_card)) hfour

/-- A nontrivial finite radical-free group with no sixteen in its order has
a nonabelian simple normal subgroup with trivial centralizer, conditional only
on the independent simple-group order-divisibility input. -/
theorem exists_simple_normal_centralizer_eq_bot
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h16 : ¬16 ∣ Nat.card G)
    (hfour : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H → 4 ∣ Nat.card H) :
    ∃ S : Subgroup G, S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ := by
  obtain ⟨S, hS, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  obtain ⟨hss, hsnc⟩ := minimal_normal_isSimple_of_radicalFree hrad h16 hfour hS
  refine ⟨S, hS.1, hss, hsnc, ?_⟩
  have : S.Normal := hS.1
  by_contra hC
  obtain ⟨T, hT, hTC⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (Subgroup.centralizer (S : Set G)) hC
  obtain ⟨hts, htnc⟩ := minimal_normal_isSimple_of_radicalFree hrad h16 hfour hT
  have hTS : T ≠ S := by
    intro he
    apply hsnc
    exact Subgroup.le_centralizer_iff_isMulCommutative.mp (he ▸ hTC)
  apply h16
  apply sixteen_dvd_of_disjoint_commuting T S
  · exact Ch09.disjoint_of_isMinimalNormal_of_ne hT hS hTS
  · intro t s
    exact (Subgroup.mem_centralizer_iff.mp (hTC t.2) s s.2).symm
  · exact hfour T hts htnc
  · exact hfour S hss hsnc

end Conjecture55Socle
end

/-! ### Module `CyclicIndexRank` -/
section
/-! Elementary abelian subgroup bounds using a cyclic subgroup of index two. -/
namespace Conjecture55CyclicIndex
universe u

end Conjecture55CyclicIndex
end

/-! ### Module `RankSocle` -/
section
/-! The almost-simple reduction using an elementary abelian rank bound instead
of the old restriction that sixteen does not divide the group order. -/
namespace Conjecture55RankSocle
open Subgroup OddOrder.Isaacs Conjecture55CyclicIndex
open scoped IsMulCommutative
universe u

end Conjecture55RankSocle
end

/-! ### Module `FTOnly.Socle` -/
section
/-! The socle is simple with trivial centralizer when a Sylow 2-subgroup has a
cyclic subgroup of index two.  Instead of Klein four subgroups, two commuting
simple factors would give a noncyclic 2-group times a group of order two, which
has no cyclic subgroup of index at most two. -/

namespace C55FT
open Subgroup OddOrder.Isaacs
universe u

/-- A noncyclic 2-group times an element of order two cannot embed in a group
whose Sylow 2-subgroup has a cyclic subgroup of index two. -/
theorem false_of_injective_prod {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (C : Subgroup P) [IsCyclic C] (hC : C.index = 2)
    {A B : Type*} [Group A] [Group B] (φ : A × B →* G) (hφ : Function.Injective φ)
    (Q : Subgroup A) [Finite Q] (hQ : IsPGroup 2 Q) (hQnc : ¬ IsCyclic Q)
    (z : B) (hz : orderOf z = 2) : False := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup B := Subgroup.zpowers z
  have hZc : Nat.card Z = 2 := by rw [Nat.card_zpowers, hz]
  let : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZc]; norm_num)
  let e : Q × Z →* A × B := Q.subtype.prodMap Z.subtype
  have he : Function.Injective e := by
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact Subtype.ext (congrArg Prod.snd h)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hn2 : 2 ≤ n := by
    by_contra h
    apply hQnc
    apply isCyclic_of_card_dvd_prime (p := 2)
    rw [hn]
    interval_cases n <;> norm_num
  have hEcard : Nat.card (Q × Z) = 2 ^ (n + 1) := by
    rw [Nat.card_prod, hn, hZc, pow_succ]
  have hE : IsPGroup 2 (Q × Z) := IsPGroup.of_card hEcard
  let g : Q × Z →* G := φ.comp e
  have hg : Function.Injective g := hφ.comp he
  have hrange : IsPGroup 2 g.range := hE.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  obtain ⟨Q', hQ'⟩ := hrange.exists_le_sylow
  let h : Q × Z →* P :=
    (Q'.equiv P).toMonoidHom.comp ((Subgroup.inclusion hQ').comp g.rangeRestrict)
  have hh : Function.Injective h := (Q'.equiv P).injective.comp
    ((Subgroup.inclusion_injective hQ').comp (by
      intro x y hxy
      exact hg (congrArg Subtype.val hxy)))
  let K : Subgroup (Q × Z) := C.comap h
  let kf : K →* C :=
    { toFun := fun x => ⟨h x, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hkf : Function.Injective kf := by
    intro x y hxy
    apply Subtype.ext
    exact hh (congrArg Subtype.val hxy)
  let : IsCyclic K := isCyclic_of_injective kf hkf
  have hKi : K.index ≤ 2 := by
    rw [show K = C.comap h from rfl, C.index_comap h]
    calc C.relIndex h.range ≤ C.relIndex ⊤ :=
          Subgroup.relIndex_le_of_le_right le_top (by rw [Subgroup.relIndex_top_right, hC]; norm_num)
      _ = C.index := Subgroup.relIndex_top_right C
      _ = 2 := hC
  have hexp : ∀ y : Q × Z, y ^ (2 ^ (n - 1)) = 1 := by
    intro y
    apply Prod.ext
    · have hd : orderOf y.1 ∣ 2 ^ n := hn ▸ orderOf_dvd_natCard y.1
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      have hkn : k ≠ n := by
        rintro rfl
        exact hQnc (isCyclic_of_orderOf_eq_card y.1 (by rw [hk', hn]))
      change y.1 ^ (2 ^ (n - 1)) = 1
      rw [← orderOf_dvd_iff_pow_eq_one, hk']
      exact pow_dvd_pow 2 (by omega)
    · change y.2 ^ (2 ^ (n - 1)) = 1
      rw [← orderOf_dvd_iff_pow_eq_one]
      have hd : orderOf y.2 ∣ 2 := hZc ▸ orderOf_dvd_natCard y.2
      exact hd.trans (dvd_pow_self 2 (by omega))
  have hKd : Nat.card K ∣ 2 ^ (n - 1) := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun y => Subtype.ext (hexp y))
  have hKle : Nat.card K ≤ 2 ^ (n - 1) := Nat.le_of_dvd (by positivity) hKd
  have hmul := K.card_mul_index
  rw [hEcard] at hmul
  have hpow : 2 ^ (n + 1) = 2 ^ (n - 1) * 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hle : Nat.card K * K.index ≤ 2 ^ (n - 1) * 2 := Nat.mul_le_mul hKle hKi
  have hpos : 0 < 2 ^ (n - 1) := by positivity
  omega

/-- No injective image of a noncyclic 2-group times an involution. -/
def NoCommutingPair (M : Type u) [Group M] : Prop :=
  ∀ (A B : Type u) [Group A] [Group B] (φ : A × B →* M), Function.Injective φ →
    ∀ (Q : Subgroup A) [Finite Q], IsPGroup 2 Q → ¬ IsCyclic Q →
      ∀ z : B, orderOf z = 2 → False

theorem noCommutingPair_of_cyclicIndex {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (C : Subgroup P) [IsCyclic C] (hC : C.index = 2) :
    NoCommutingPair G :=
  fun _ _ _ _ φ hφ Q _ hQ hnc z hz => false_of_injective_prod P C hC φ hφ Q hQ hnc z hz

theorem noCommutingPair_of_injective {M G : Type u} [Group M] [Group G]
    (f : M →* G) (hf : Function.Injective f) (hG : NoCommutingPair G) :
    NoCommutingPair M :=
  fun A B _ _ φ hφ Q _ hQ hnc z hz => hG A B (f.comp φ) (hf.comp hφ) Q hQ hnc z hz

/-- The input about nonabelian simple groups supplied by the odd order theorem. -/
def SimpleTwoFacts (H : Type u) [Group H] : Prop :=
  (∃ Q : Subgroup H, IsPGroup 2 Q ∧ ¬ IsCyclic Q) ∧ ∃ x : H, orderOf x = 2

theorem false_of_commuting_simple {M : Type u} [Group M] [Finite M]
    (hno : NoCommutingPair M) (T S : Subgroup M) (hd : Disjoint T S)
    (hc : ∀ (t : T) (s : S), Commute (t : M) (s : M))
    (hT : SimpleTwoFacts T) (hS : SimpleTwoFacts S) : False := by
  obtain ⟨⟨Q, hQ, hQnc⟩, -⟩ := hT
  obtain ⟨-, ⟨z, hz⟩⟩ := hS
  let φ : T × S →* M := T.subtype.noncommCoprod S.subtype hc
  have hφ : Function.Injective φ := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    exact ⟨T.subtype_injective, S.subtype_injective, by simpa using hd⟩
  exact hno T S φ hφ Q hQ hQnc z hz

theorem simple_of_semisimple_noCommutingPair
    {M : Type u} [Group M] [Finite M] [Nontrivial M]
    (hss : Ch09.IsSemisimpleGroup M) (hno : NoCommutingPair M)
    (hsimple : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬ IsMulCommutative H → SimpleTwoFacts H) :
    IsSimpleGroup M ∧ ¬ IsMulCommutative M := by
  classical
  obtain ⟨X, hX, hsup⟩ := hss
  have hne : X.Nonempty := by
    by_contra h
    have he : X = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, sSup_empty] at hsup
    exact bot_ne_top hsup
  obtain ⟨S, hS⟩ := hne
  have hu : ∀ T ∈ X, T = S := by
    intro T hT
    by_contra hTS
    exact false_of_commuting_simple hno T S
      (Ch09.disjoint_of_isMinimalNormal_of_ne
        (Ch09.isMinimalNormal_of_mem_semisimpleFamily hX hT)
        (Ch09.isMinimalNormal_of_mem_semisimpleFamily hX hS) hTS)
      (fun t s => Ch09.commute_of_mem_semisimpleFamily_of_ne hX hT hS hTS t.2 s.2)
      (hsimple T (hX T hT).2.1 (hX T hT).2.2) (hsimple S (hX S hS).2.1 (hX S hS).2.2)
  have hXS : X = {S} := Set.eq_singleton_iff_unique_mem.mpr ⟨hS, hu⟩
  have hStop : S = ⊤ := by simpa [hXS] using hsup
  let e : S ≃* M := (MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv
  have : IsSimpleGroup S := (hX S hS).2.1
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  intro hcomm
  let : IsMulCommutative M := hcomm
  exact (hX S hS).2.2
    (Ch09.isMulCommutative_of_surjective e.symm.toMonoidHom e.symm.surjective)

theorem minimal_normal_isSimple_noCommutingPair
    {G : Type u} [Group G] [Finite G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hno : NoCommutingPair G)
    (hsimple : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬ IsMulCommutative H → SimpleTwoFacts H)
    {N : Subgroup G} (hN : Ch02.IsMinimalNormal N) :
    IsSimpleGroup N ∧ ¬ IsMulCommutative N := by
  have hnc : ¬ IsMulCommutative N := by
    intro hcomm
    let : IsMulCommutative N := hcomm
    exact hN.2.1 (hrad N hN.1 inferInstance)
  have hss := (Ch09.isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hN).resolve_left hnc
  have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN.2.1
  exact simple_of_semisimple_noCommutingPair hss
    (noCommutingPair_of_injective N.subtype N.subtype_injective hno) hsimple

/-- The socle is nonabelian simple with trivial centralizer when a Sylow
2-subgroup has a cyclic subgroup of index two. -/
theorem exists_simple_normal_centralizer_eq_bot_of_cyclicIndex
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (P : Sylow 2 G) (C : Subgroup P) [IsCyclic C] (hC : C.index = 2)
    (hsimple : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬ IsMulCommutative H → SimpleTwoFacts H) :
    ∃ S : Subgroup G, S.Normal ∧ IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ := by
  have hno := noCommutingPair_of_cyclicIndex P C hC
  obtain ⟨S, hS, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  obtain ⟨hss, hsnc⟩ := minimal_normal_isSimple_noCommutingPair hrad hno hsimple hS
  refine ⟨S, hS.1, hss, hsnc, ?_⟩
  have : S.Normal := hS.1
  by_contra hCS
  obtain ⟨T, hT, hTC⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (Subgroup.centralizer (S : Set G)) hCS
  obtain ⟨hts, htnc⟩ := minimal_normal_isSimple_noCommutingPair hrad hno hsimple hT
  have hTS : T ≠ S := by
    intro he
    apply hsnc
    exact Subgroup.le_centralizer_iff_isMulCommutative.mp (he ▸ hTC)
  exact false_of_commuting_simple hno T S
    (Ch09.disjoint_of_isMinimalNormal_of_ne hT hS hTS)
    (fun t s => (Subgroup.mem_centralizer_iff.mp (hTC t.2) s s.2).symm)
    (hsimple T hts htnc) (hsimple S hss hsnc)

variable (hFT : OddOrderTheorem)
include hFT

theorem simpleTwoFacts_of_oddOrder (H : Type) [Group H] [Finite H]
    (hs : IsSimpleGroup H) (hn : ¬ IsMulCommutative H) : SimpleTwoFacts H := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 H := default
  exact ⟨⟨Q, Q.isPGroup', not_isCyclic_sylow_two_of_simple hFT H hs hn Q⟩,
    exists_involution_of_simple hFT H hs hn⟩

end C55FT
end

/-! ### Module `ExponentShape` -/
section
/-! The odd part of a strict FC counterexample using the Sylow exponent bound. -/
namespace Conjecture55ExponentShape
open Conjecture55Lean4Web Conjecture55Lean4Web

/-- The ordinary Frobenius lower bound already restricts the odd part of a
strict counterexample. For 2-part at least sixteen it is squarefree; for
smaller 2-parts at most one odd prime is repeated, and only to exponent two. -/
theorem odd_part_shape_of_noncyclic_sylow
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ((a = 2 ∨ a = 3) ∧ (∀ p, m.factorization p ≤ 2) ∧
      ∀ p q, 2 ≤ m.factorization p → 2 ≤ m.factorization q → p = q) ∨
    ((a = 4 ∨ a = 5) ∧ Squarefree m) := by
  have hcount := RootWeights.cyclic_count_ge_of_noncyclic_sylow ha hm P hnc hcard hbase
  have ha5 := RootWeights.two_part_le_five_of_noncyclic_sylow ha hm P hnc hcard hbase hlt
  have h2 : ¬2 ∣ m := by
    simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm
  have hω : numPrimeFactors G = m.primeFactors.card + 1 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
    rw [hcard]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 a m Nat.prime_two
      (by omega) hm.pos h2
  have hexp : 2 ^ (numPrimeFactors G + 2) = 8 * 2 ^ m.primeFactors.card := by
    rw [hω, show m.primeFactors.card + 1 + 2 = m.primeFactors.card + 3 by omega,
      pow_add]
    ring
  have hsmall : (a + 2) * m.divisors.card < 8 * 2 ^ m.primeFactors.card := by
    simpa only [hexp] using hcount.trans_lt hlt
  by_cases ha4 : 4 ≤ a
  · right
    refine ⟨by omega, squarefree_of_six_mul_card_divisors_lt m hm.pos ?_⟩
    exact (Nat.mul_le_mul_right _ (by omega : 6 ≤ a + 2)).trans_lt hsmall
  · left
    refine ⟨by omega, factorization_shape_of_four_mul_card_divisors_lt m hm.pos ?_⟩
    exact (Nat.mul_le_mul_right _ (by omega : 4 ≤ a + 2)).trans_lt hsmall

end Conjecture55ExponentShape
end

/-! ### Module `FTOnly.Closure` -/
section
/-! # Conjecture 5.5 from the odd order theorem

The only external input is the Feit–Thompson odd order theorem, taken as the
explicit hypothesis `OddOrderTheorem`.  No Gorenstein–Walter classification,
Brauer–Suzuki theorem, or other classification result is assumed. -/

namespace C55FT
open Conjecture55Lean4Web

theorem radicalFree_lower_bound_of_oddOrder (hFT : OddOrderTheorem) (G : Type) [Group G]
    [Fintype G] (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hns : ¬ Group.IsSolvable G) : 2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  classical
  by_contra hbound
  have hlt := Nat.lt_of_not_ge hbound
  have hnt : Nontrivial G := by
    by_contra h
    let : Subsingleton G := not_nontrivial_iff_subsingleton.mp h
    exact hns inferInstance
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := G)).ne'
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := default
  have hnc := not_isCyclic_sylow_two_of_radicalFree hFT G hrad P
  have hPc : Nat.card P = 2 ^ a := RootWeights.sylow_card_eq_two_part P hm hcard
  have h4P := four_dvd_card_of_not_isCyclic P.isPGroup' hnc
  have ha : 2 ≤ a := by
    change 4 ∣ Nat.card P at h4P
    rw [hPc] at h4P
    by_contra h
    interval_cases a <;> norm_num at h4P
  have hmo := Nat.odd_iff.mp hm
  have hfour : ∀ (H : Type) [Group H] [Finite H],
      IsSimpleGroup H → ¬ IsMulCommutative H → 4 ∣ Nat.card H :=
    fun H _ _ hs hn => four_dvd_card_of_simple hFT H hs hn
  rcases Conjecture55ExponentShape.odd_part_shape_of_noncyclic_sylow ha hm P hnc hcard
      (Conjecture55FrobeniusProof.rootCountLowerBound G) hlt with ⟨ha23, -, -⟩ | ⟨ha45, hsf⟩
  · have h16 : ¬ 16 ∣ Nat.card G := by
      rw [hcard]
      rcases ha23 with rfl | rfl <;> omega
    obtain ⟨S, hSn, hSs, hSc, hC⟩ :=
      Conjecture55Socle.exists_simple_normal_centralizer_eq_bot hrad h16 hfour
    let : S.Normal := hSn
    have h4S : 4 ∣ Nat.card S := four_dvd_card_of_simple hFT S hSs hSc
    rcases ha23 with rfl | rfl
    · exact false_of_four_two_part hFT hrad hm hcard P hnc S hSs hSc h4S hC hlt
    · exact false_of_eight_two_part hrad hm hcard P hnc S hSs hSc h4S hC hlt
  · obtain ⟨C, hCcyc, hCidx⟩ := RootWeights.exists_cyclic_index_two_of_strict_fc_bound
      (by omega) hm P hnc hcard (Conjecture55FrobeniusProof.rootCountLowerBound G) hlt
    let : IsCyclic C := hCcyc
    obtain ⟨S, hSn, hSs, hSc, hC⟩ := exists_simple_normal_centralizer_eq_bot_of_cyclicIndex hrad
      P C hCidx (fun H _ _ hs hn => simpleTwoFacts_of_oddOrder hFT H hs hn)
    let : S.Normal := hSn
    have h4S : 4 ∣ Nat.card S := four_dvd_card_of_simple hFT S hSs hSc
    exact false_of_large_two_part (by omega) hm hsf hcard P hnc S hSs hSc h4S hC hlt

theorem nonsolvable_lower_bound_of_oddOrder (hFT : OddOrderTheorem) :
    NonSolvableLowerBound :=
  lower_bound_of_radicalFree_case (radicalFree_lower_bound_of_oddOrder hFT)

/-- **Das–Dey–Sharma Conjecture 5.5 follows from the odd order theorem**, with
exactly the Formal Conjectures quantifiers, definitions, and strict bound. -/
theorem conjecture55_of_oddOrder (hFT : OddOrderTheorem) :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  affirmative_target_of_lower_bound (nonsolvable_lower_bound_of_oddOrder hFT)

/-- The same statement with the odd order hypothesis written out. -/
theorem solvable_of_cyc_lt_of_oddOrder
    (hFT : ∀ (H : Type) [Group H] [Finite H], Odd (Nat.card H) → Group.IsSolvable H) :
    ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  (conjecture55_of_oddOrder hFT).mp trivial

end C55FT
end

/-! ## Final statement

Formal Conjectures, `Arxiv.«2604.08040».solvable_of_cyc_lt`, with the definitions
of `cyc` and `numPrimeFactors` unfolded, assuming the odd order theorem. -/
theorem conjecture55_of_oddOrder_unfolded
    (hFT : ∀ (H : Type) [Group H] [Finite H], Odd (Nat.card H) → Group.IsSolvable H) :
    ∀ (G : Type) [Group G] [Fintype G],
      Nat.card {H : Subgroup G // IsCyclic H} <
        2 ^ ((Fintype.card G).primeFactors.card + 2) → Group.IsSolvable G :=
  C55FT.solvable_of_cyc_lt_of_oddOrder hFT

/-- The same theorem, with the hypothesis written exactly as the statement of the
Lean Eval problem `feit_thompson` (`LeanEval.GroupTheory.feit_thompson`, which is
stated for `G : Type*`; it is used here for `G : Type`). -/
theorem conjecture55_of_leanEval_feit_thompson
    (feit_thompson : ∀ {G : Type} [Group G] [Finite G],
      Odd (Nat.card G) → Group.IsSolvable G) :
    ∀ (G : Type) [Group G] [Fintype G],
      Nat.card {H : Subgroup G // IsCyclic H} <
        2 ^ ((Fintype.card G).primeFactors.card + 2) → Group.IsSolvable G :=
  conjecture55_of_oddOrder_unfolded fun _ _ _ h => feit_thompson h

#print axioms conjecture55_of_oddOrder_unfolded
#print axioms conjecture55_of_leanEval_feit_thompson
