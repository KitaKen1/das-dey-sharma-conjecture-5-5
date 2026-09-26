/-
Copyright 2026 The Formal Conjectures Authors and contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
The target and, in the standalone version, the two definitions are adapted from
FormalConjectures/Arxiv/2604.08040/Conjecture5_5.lean at
8323e878b83fcd7f4a448256069352a265460d75.
-/

import Mathlib

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

omit [Finite G] [Finite H] in
/-- The last transfer step of the draft, given an embedding and a bound for H.
The equality of the numbers of prime factors is a necessary explicit input. -/
theorem lower_bound_of_embedding [Fintype G] [Fintype H] (f : H →* G) (hf : Function.Injective f)
    (hprimes : numPrimeFactors H = numPrimeFactors G)
    (hbound : 2 ^ (numPrimeFactors H + 2) ≤ cyc H) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  rw [← hprimes]
  exact hbound.trans (cyc_le_of_injective f hf)

end CyclicSubgroups

/-- Quotient monotonicity, the first elementary ingredient of the proof draft. -/
theorem cyc_quotient_le (G : Type*) [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] : cyc (G ⧸ N) ≤ cyc G := by
  exact cyc_le_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

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

#print axioms two_lifts

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

#print axioms normal_hall_doubling
#print axioms two_mul_card_le_of_two_lifts
#print axioms two_cyclic_lifts
#print axioms coprime_semidirect_doubling

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

#print axioms generatorsEquiv
#print axioms card_generators

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

#print axioms cyclic_count_eq_sum

/-- Element-order divisibility along a bijection reverses cyclic subgroup counts. -/
theorem cyclic_count_le_of_order_dvd_equiv
    {H : Type*} [Group H] [Fintype H] (e : G ≃ H)
    (he : ∀ x : G, orderOf x ∣ orderOf (e x)) :
    Nat.card (CyclicSubgroups H) ≤ Nat.card (CyclicSubgroups G) := by
  have hsum : (Nat.card (CyclicSubgroups H) : ℚ) ≤
      (Nat.card (CyclicSubgroups G) : ℚ) := by
    rw [cyclic_count_eq_sum, cyclic_count_eq_sum, ← e.sum_comp]
    apply Finset.sum_le_sum
    intro x _
    have hposx : 0 < Nat.totient (orderOf x) := Nat.totient_pos.mpr (orderOf_pos x)
    have hpose : 0 < Nat.totient (orderOf (e x)) := Nat.totient_pos.mpr (orderOf_pos _)
    exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hposx)
      (Nat.cast_le.mpr (Nat.le_of_dvd hpose (Nat.totient_dvd_of_dvd (he x))))
  exact_mod_cast hsum

#print axioms cyclic_count_le_of_order_dvd_equiv

end

end CyclicSum

/-- The exact FC cyclic-subgroup count as a sum over elements. -/
theorem cyc_eq_sum (G : Type*) [Group G] [Fintype G] :
    (cyc G : ℚ) = ∑ x : G, (1 : ℚ) / Nat.totient (orderOf x) :=
  CyclicSum.cyclic_count_eq_sum

/-- The counting consequence of an order-divisibility bijection. The existence
of Amiri's bijection is a separate, still unformalized theorem. -/
theorem cyc_le_of_order_dvd_equiv {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (e : G ≃ H)
    (he : ∀ x : G, orderOf x ∣ orderOf (e x)) : cyc H ≤ cyc G :=
  CyclicSum.cyclic_count_le_of_order_dvd_equiv e he

#print axioms cyc_eq_sum
#print axioms cyc_le_of_order_dvd_equiv

section Arithmetic

/-- The arithmetic part of removing a coprime normal p-subgroup.
The group-theoretic inequality cG ≥ 2*cH remains an input here. -/
theorem lower_bound_after_doubling (t cG cH : ℕ) (ht : 1 ≤ t)
    (hdouble : 2 * cH ≤ cG) (hbound : 2 ^ ((t - 1) + 2) ≤ cH) :
    2 ^ (t + 2) ≤ cG := by
  have hexp : t + 2 = ((t - 1) + 2) + 1 := by omega
  calc
    2 ^ (t + 2) = 2 * 2 ^ ((t - 1) + 2) := by
      rw [hexp, pow_succ, Nat.mul_comm]
    _ ≤ 2 * cH := Nat.mul_le_mul_left 2 hbound
    _ ≤ cG := hdouble

/-- Arithmetic consequence of Amiri's lower bound.
Here d represents τ(m), and t is the number of distinct prime factors of |G|.
This theorem does not establish Amiri's theorem or its applicability. -/
theorem two_part_exponent_restriction (a d t : ℕ) (ha : 2 ≤ a) (ht : 1 ≤ t)
    (hd : 2 ^ (t - 1) ≤ d) (hsmall : 2 * a * d < 2 ^ (t + 2)) :
    a = 2 ∨ a = 3 := by
  have hexp : t + 2 = (t - 1) + 3 := by omega
  have hpow : 2 ^ (t + 2) = 8 * 2 ^ (t - 1) := by
    rw [hexp, pow_add]
    ring
  have hpos : 0 < 2 ^ (t - 1) := by positivity
  have hmul := Nat.mul_le_mul_left (2 * a) hd
  rw [hpow] at hsmall
  have halt : a < 4 := by nlinarith
  omega

/-- Numeric sum used at the A5 boundary. This does not count subgroups of A5. -/
theorem a5_count_arithmetic : 1 + 15 + 10 + 6 = 2 ^ (3 + 2) := by norm_num

/-- Numeric comparison in the J1 case. The normalizer data are not proved here. -/
theorem j1_count_arithmetic : 175560 / 114 = 1540 ∧ 2 ^ (6 + 2) < 1540 := by
  norm_num

/-- Sum of the three types of cyclic subgroups and the identity, over ℚ.
The distinctness and group-theoretic interpretation are not established here. -/
theorem psl2_count_sum (p : ℚ) :
    p * (p + 1) / 2 + p * (p - 1) / 2 + (p + 1) + 1 = p ^ 2 + p + 2 := by
  ring

/-- The final strict inequality used for PSL2(p), after the prime-factor bound. -/
theorem psl2_final_arithmetic (p : ℚ) (hp : 7 ≤ p) :
    (2 / 3 : ℚ) * (p ^ 2 - 1) < p ^ 2 + p + 2 := by
  nlinarith [sq_nonneg p]

/-- If a positive integer is a multiple of six and exceeds six, the product
of one factor of two for each distinct prime factor is at most a third of it. -/
theorem three_mul_two_pow_card_primeFactors_le (n : ℕ) (hn : 6 < n) (h6 : 6 ∣ n) :
    3 * 2 ^ n.primeFactors.card ≤ n := by
  have hn0 : n ≠ 0 := by omega
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num) h6, hn0⟩
  have h3 : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_trans (by norm_num) h6, hn0⟩
  by_cases hs : n.primeFactors ⊆ {2, 3}
  · have heq : n.primeFactors = {2, 3} := by
      apply Finset.Subset.antisymm hs
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    rw [heq]
    norm_num
    obtain ⟨k, rfl⟩ := h6
    omega
  · obtain ⟨q, hq, hq23⟩ := Finset.not_subset.mp hs
    have hqs : q ≠ 2 ∧ q ≠ 3 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hq23
    have hq2 := hqs.1
    have hq3 := hqs.2
    have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
    have hq5 : 5 ≤ q := by
      have hqge := hqprime.two_le
      have hq4 : q ≠ 4 := by intro h; subst q; norm_num at hqprime
      omega
    have h32 : 3 ∈ n.primeFactors.erase 2 := by simp [h3]
    have hq32 : q ∈ (n.primeFactors.erase 2).erase 3 := by simp [hq, hq2, hq3]
    let s := ((n.primeFactors.erase 2).erase 3).erase q
    have hcard : n.primeFactors.card = s.card + 3 := by
      have hA := Finset.card_erase_add_one h2
      have hB := Finset.card_erase_add_one h32
      have hC := Finset.card_erase_add_one hq32
      dsimp [s]
      omega
    have hprod : (∏ x ∈ n.primeFactors, x) = 6 * q * ∏ x ∈ s, x := by
      rw [← Finset.mul_prod_erase _ _ h2, ← Finset.mul_prod_erase _ _ h32,
        ← Finset.mul_prod_erase _ _ hq32]
      dsimp [s]
      ring
    have hsmall : 2 ^ s.card ≤ ∏ x ∈ s, x := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun _ _ => by omega)
      intro x hx
      have hxn : x ∈ n.primeFactors :=
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      exact (Nat.mem_primeFactors.mp hxn).1.two_le
    calc
      3 * 2 ^ n.primeFactors.card = 24 * 2 ^ s.card := by rw [hcard, pow_add]; ring
      _ ≤ 24 * ∏ x ∈ s, x := Nat.mul_le_mul_left 24 hsmall
      _ ≤ 6 * q * ∏ x ∈ s, x := Nat.mul_le_mul_right _ (by omega)
      _ = ∏ x ∈ n.primeFactors, x := hprod.symm
      _ ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)

/-- Prime squares above three are congruent to one modulo twenty-four. -/
theorem prime_sq_mod_twentyfour (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ^ 2 % 24 = 1 := by
  have hp2 : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).mpr (by omega)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have heq : p = 3 := (hp.dvd_iff_eq (by omega)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  rw [Nat.pow_mod]
  have hlt : p % 24 < 24 := Nat.mod_lt _ (by omega)
  interval_cases h : p % 24 <;> omega

/-- The arithmetic PSL₂ threshold, using its numerical order formula only.
The theorem makes no group-theoretic subgroup-count assumptions. -/
theorem psl2_primeFactor_threshold (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    2 ^ ((p * (p ^ 2 - 1) / 2).primeFactors.card + 2) < p ^ 2 + p + 2 := by
  have hmod := prime_sq_mod_twentyfour p hp (by omega)
  have h24 : 24 ∣ p ^ 2 - 1 := by omega
  obtain ⟨k, hk⟩ := h24
  let n := 6 * k
  have hNval : p ^ 2 - 1 = 4 * n := by dsimp [n]; omega
  have hpSq : 1 ≤ p ^ 2 := by nlinarith
  have hN6 : 6 ∣ n := ⟨k, rfl⟩
  have hNgt : 6 < n := by dsimp [n]; nlinarith [Nat.sub_add_cancel hpSq]
  have hN0 : n ≠ 0 := by omega
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num) hN6, hN0⟩
  have horder : p * (p ^ 2 - 1) / 2 = p * (2 * n) := by
    rw [hNval, show p * (4 * n) = 2 * (p * (2 * n)) by ring]
    omega
  have hpf2N : (2 * n).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_mul (by omega) hN0, Nat.prime_two.primeFactors]
    exact Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr h2)
  have hcard : (p * (p ^ 2 - 1) / 2).primeFactors.card ≤ n.primeFactors.card + 1 := by
    rw [horder, Nat.primeFactors_mul hp.ne_zero (by omega), hp.primeFactors, hpf2N]
    simpa using Finset.card_insert_le p n.primeFactors
  have hpow : 2 ^ ((p * (p ^ 2 - 1) / 2).primeFactors.card + 2) ≤
      8 * 2 ^ n.primeFactors.card := by
    calc
      _ ≤ 2 ^ (n.primeFactors.card + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 8 * 2 ^ n.primeFactors.card := by rw [pow_add]; ring
  have hbound := three_mul_two_pow_card_primeFactors_le n hNgt hN6
  nlinarith [Nat.sub_add_cancel hpSq]

/-- The exceptional smallest prime attains the numerical threshold exactly. -/
theorem psl2_five_primeFactor_threshold :
    2 ^ ((5 * (5 ^ 2 - 1) / 2).primeFactors.card + 2) = 5 ^ 2 + 5 + 2 := by
  have h60 : (60 : ℕ).primeFactors = {2, 3, 5} := by
    rw [show (60 : ℕ) = 2 * (2 * (3 * 5)) by norm_num]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num)]
    norm_num [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors,
      (by norm_num : Nat.Prime 5).primeFactors]
    decide
  change 2 ^ ((60 : ℕ).primeFactors.card + 2) = 32
  rw [h60]
  norm_num

/-- All primes at least five satisfy the threshold, including the equality
at five and the strict bound above it. -/
theorem psl2_primeFactor_threshold_le (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    2 ^ ((p * (p ^ 2 - 1) / 2).primeFactors.card + 2) ≤ p ^ 2 + p + 2 := by
  by_cases h5 : p = 5
  · subst p
    exact psl2_five_primeFactor_threshold.le
  · have h6 : p ≠ 6 := by intro h; subst p; norm_num at hp
    exact (psl2_primeFactor_threshold p hp (by omega)).le

/-- Division form of the distinct-prime estimate. -/
theorem two_pow_card_primeFactors_le_div_three (n : ℕ) (hn : 6 < n) (h6 : 6 ∣ n) :
    2 ^ n.primeFactors.card ≤ n / 3 := by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  simpa [Nat.mul_comm] using three_mul_two_pow_card_primeFactors_le n hn h6

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

#print axioms card_primeFactors_prime_pow_mul_of_not_dvd
#print axioms card_primeFactors_prime_pow_mul_of_dvd
#print axioms psl2_five_primeFactor_threshold
#print axioms psl2_primeFactor_threshold_le
#print axioms two_pow_card_primeFactors_le_div_three
#print axioms psl2_primeFactor_threshold
#print axioms three_mul_two_pow_card_primeFactors_le
#print axioms prime_sq_mod_twentyfour

/-- Each prime in the factorization contributes at least two divisors. -/
theorem pow_card_le_prod_factorization_succ (m : ℕ) (s : Finset ℕ)
    (hs : s ⊆ m.primeFactors) :
    2 ^ s.card ≤ ∏ p ∈ s, (m.factorization p + 1) := by
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => by omega)
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

#print axioms two_pow_card_primeFactors_le_card_divisors
#print axioms two_prime_factor_divisor_count_bound
#print axioms factorization_shape_of_four_mul_card_divisors_lt
#print axioms pow_card_le_prod_factorization_succ
#print axioms prime_factor_divisor_count_bound
#print axioms squarefree_of_six_mul_card_divisors_lt

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

#print axioms no_normal_p_subgroup_of_minimal_counterexample

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

#print axioms exists_last_derived
#print axioms exists_characteristic_p_subgroup
#print axioms exists_normal_p_subgroup_of_solvable_normal

/-- Excluding nontrivial normal p-subgroups excludes all nontrivial solvable normal subgroups. -/
theorem solvable_normal_eq_bot_of_no_normal_p_subgroup [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∀ N : Subgroup G,
      N.Normal → IsPGroup p N → N = ⊥)
    (R : Subgroup G) [R.Normal] [Group.IsSolvable R] : R = ⊥ := by
  by_contra hR
  obtain ⟨p, hp, N, hN, hn, hpN⟩ := exists_normal_p_subgroup_of_solvable_normal R hR
  exact hN (h p hp N hn hpN)

#print axioms solvable_normal_eq_bot_of_no_normal_p_subgroup

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

#print axioms minimal_counterexample_solvable_normal_eq_bot
#print axioms lower_bound_of_radicalFree_case


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

#print axioms normalizer_le_centralizer_of_aut_isPGroup
#print axioms exists_normal_complement_of_aut_isPGroup

theorem cyclic_or_kleinFour_of_card_four
    {G : Type*} [Group G] (hcard : Nat.card G = 4) :
    IsCyclic G ∨ IsKleinFour G := by
  by_cases hcyc : IsCyclic G
  · exact Or.inl hcyc
  · exact Or.inr ⟨hcard,
      (not_isCyclic_iff_exponent_eq_prime Nat.prime_two (by simpa using hcard)).mp hcyc⟩

#print axioms cyclic_or_kleinFour_of_card_four

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

theorem cyclic_count_prod_of_coprime (h : Nat.Coprime (Nat.card G) (Nat.card H)) :
    Nat.card (CyclicSubgroups (G × H)) =
      Nat.card (CyclicSubgroups G) * Nat.card (CyclicSubgroups H) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite H
  have hord (x : G) (y : H) : Nat.Coprime (orderOf x) (orderOf y) :=
    h.of_dvd (orderOf_dvd_natCard x) (orderOf_dvd_natCard y)
  have hq : (Nat.card (CyclicSubgroups (G × H)) : ℚ) =
      (Nat.card (CyclicSubgroups G) : ℚ) * Nat.card (CyclicSubgroups H) := by
    rw [cyclic_count_eq_sum, cyclic_count_eq_sum, cyclic_count_eq_sum,
      Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Prod.orderOf_mk, (hord x y).lcm_eq_mul, Nat.totient_mul (hord x y), Nat.cast_mul]
    ring
  exact_mod_cast hq

theorem cyclic_count_eq_card_of_exponent_two (h : ∀ x : G, x ^ 2 = 1) :
    Nat.card (CyclicSubgroups G) = Nat.card G := by
  classical
  let := Fintype.ofFinite G
  have ht (x : G) : Nat.totient (orderOf x) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (h x)) with h1 | h2
    · simp [h1]
    · simp [h2]
  have hq : (Nat.card (CyclicSubgroups G) : ℚ) = Nat.card G := by
    rw [cyclic_count_eq_sum]
    simp [ht, Nat.card_eq_fintype_card]
  exact_mod_cast hq

#print axioms cyclic_count_eq_divisors_card
#print axioms cyclic_count_prod_of_coprime
#print axioms cyclic_count_eq_card_of_exponent_two
end
end CyclicSum


namespace TwoFactor
noncomputable section


theorem totient_lcm_two (n : ℕ) : (Nat.lcm n 2).totient = n.totient := by
  by_cases h : 2 ∣ n
  · rw [Nat.lcm_eq_left h]
  · have hc : n.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h).symm
    rw [hc.lcm_eq_mul, Nat.mul_comm, Nat.totient_two_mul_of_odd]
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using h)

theorem totient_orderOf_prod_card_two
    {G H : Type*} [Group G] [Group H] (hH : Nat.card H = 2) (g : G) (h : H) :
    (orderOf (g,h)).totient = (orderOf g).totient := by
  have hd : orderOf h ∣ 2 := hH ▸ orderOf_dvd_natCard h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
  · simp [Prod.orderOf, hh]
  · simp [Prod.orderOf, hh, totient_lcm_two]

/-- Multiplying any finite group by a group of order two doubles its cyclic count. -/
theorem cyc_prod_card_two
    {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (hH : Nat.card H = 2) : cyc (G × H) = 2 * cyc G := by
  have heq : (cyc (G × H) : ℚ) = 2 * (cyc G : ℚ) := by
    change (Nat.card (CyclicSum.CyclicSubgroups (G × H)) : ℚ) =
      2 * (Nat.card (CyclicSum.CyclicSubgroups G) : ℚ)
    rw [CyclicSum.cyclic_count_eq_sum, CyclicSum.cyclic_count_eq_sum, Fintype.sum_prod_type]
    simp_rw [totient_orderOf_prod_card_two hH]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card, hH]
    simp only [Nat.cast_ofNat, ← Finset.mul_sum]
  exact_mod_cast heq

#print axioms totient_lcm_two
#print axioms totient_orderOf_prod_card_two
#print axioms cyc_prod_card_two
end
end TwoFactor


namespace ComparisonModel
open TwoFactor
noncomputable section

lemma card_divisors_two_pow_mul (k m : ℕ) (hm : Odd m) :
    (2 ^ k * m).divisors.card = (k + 1) * m.divisors.card := by
  rw [(hm.coprime_two_left.pow_left k).card_divisors_mul,
    Nat.divisors_prime_pow Nat.prime_two]
  simp

lemma cyc_of_isCyclic (G : Type*) [Group G] [Finite G] [IsCyclic G] :
    cyc G = (Nat.card G).divisors.card :=
  CyclicSum.cyclic_count_eq_divisors_card

/-- The exact cyclic count of the group in Amiri's p=2 comparison. -/
theorem comparison_cyclic_count {K H : Type*} [Group K] [Group H]
    [Fintype K] [Fintype H] [IsCyclic K]
    (a m : ℕ) (ha : 1 ≤ a) (hm : Odd m)
    (hK : Nat.card K = 2 ^ (a - 1) * m) (hH : Nat.card H = 2) :
    cyc (K × H) = 2 * a * m.divisors.card := by
  rw [cyc_prod_card_two hH, cyc_of_isCyclic, hK, card_divisors_two_pow_mul _ _ hm]
  have he : a - 1 + 1 = a := by omega
  rw [he]
  ring

/-- Once the order-divisibility bijection has been constructed, the group
bound c(G) >= 2 a tau(m) follows with no further counting hypotheses. -/
theorem cyclic_count_lower_bound_of_comparison
    {G K H : Type*} [Group G] [Group K] [Group H]
    [Fintype G] [Fintype K] [Fintype H] [IsCyclic K]
    (a m : ℕ) (ha : 1 ≤ a) (hm : Odd m)
    (hK : Nat.card K = 2 ^ (a - 1) * m) (hH : Nat.card H = 2)
    (e : G ≃ K × H) (he : ∀ x : G, orderOf x ∣ orderOf (e x)) :
    2 * a * m.divisors.card ≤ cyc G := by
  rw [← comparison_cyclic_count a m ha hm hK hH]
  exact CyclicSum.cyclic_count_le_of_order_dvd_equiv e he

#print axioms card_divisors_two_pow_mul
#print axioms cyc_of_isCyclic
#print axioms comparison_cyclic_count
#print axioms cyclic_count_lower_bound_of_comparison
end
end ComparisonModel


namespace ElementaryCollapse
open TwoFactor
noncomputable section

lemma dvd_two_mul_of_dvd_four_mul {n m : ℕ} (hd : n ∣ 4 * m) (h4 : ¬ 4 ∣ n) :
    n ∣ 2 * m := by
  by_cases h2 : 2 ∣ n
  · obtain ⟨k, rfl⟩ := h2
    have hk : ¬ 2 ∣ k := by
      intro he
      apply h4
      obtain ⟨j, rfl⟩ := he
      exact ⟨j, by ring⟩
    have hd' : k ∣ 2 * m := by
      apply (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp
      convert hd using 1
      ring
    have hkm : k ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr hk).symm.dvd_of_dvd_mul_left hd'
    exact Nat.mul_dvd_mul_left 2 hkm
  · have hc : n.Coprime 4 := by
      simpa using (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm.pow_right 2
    exact dvd_mul_of_dvd_right (hc.dvd_of_dvd_mul_left hd) 2

/-- Collapse the four-torsion of the comparison factor to exponent two.
The original group has no element order divisible by four. -/
theorem exists_order_dvd_equiv_of_no_four
    {G B E C : Type*} [Group G] [Group B] [Group E] [Group C]
    [Fintype G] [Fintype B] [Fintype E] [Fintype C]
    (hcard : Nat.card B = Nat.card E)
    (hB : ∀ b : B, b ^ 4 = 1) (hE : ∀ e : E, e ^ 2 = 1)
    (hC : Odd (Nat.card C)) (hG : ∀ g : G, ¬ 4 ∣ orderOf g)
    (f : G ≃ B × C) (hf : ∀ g : G, orderOf g ∣ orderOf (f g)) :
    ∃ e : G ≃ E × C, ∀ g : G, orderOf g ∣ orderOf (e g) := by
  classical
  obtain ⟨θ₀⟩ := Finite.card_eq.mp hcard
  let θ : B ≃ E := θ₀.setValue 1 1
  have hθ : θ 1 = 1 := by simp [θ]
  refine ⟨f.trans (θ.prodCongr (Equiv.refl C)), ?_⟩
  intro g
  change orderOf g ∣ orderOf (θ (f g).1, (f g).2)
  have hd : orderOf g ∣ Nat.lcm (orderOf (f g).1) (orderOf (f g).2) := by
    simpa only [Prod.orderOf] using hf g
  by_cases hb : (f g).1 = 1
  · simpa [hb, hθ, Prod.orderOf] using hd
  · have hθb : θ (f g).1 ≠ 1 := by
      intro h
      exact hb (θ.injective (h.trans hθ.symm))
    have hθord : orderOf (θ (f g).1) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp
        (orderOf_dvd_of_pow_eq_one (hE (θ (f g).1))) with hh | hh
      · exact False.elim (hθb (orderOf_eq_one_iff.mp hh))
      · exact hh
    have hco : (orderOf (f g).2).Coprime 2 :=
      hC.coprime_two_right.coprime_dvd_left (orderOf_dvd_natCard _)
    rw [Prod.orderOf_mk, hθord, hco.symm.lcm_eq_mul]
    apply dvd_two_mul_of_dvd_four_mul _ (hG g)
    exact hd.trans (Nat.lcm_dvd
      (dvd_mul_of_dvd_left (orderOf_dvd_of_pow_eq_one (hB (f g).1)) _)
      (by exact ⟨4, by ring⟩))

/-- The elementary order-eight comparison yields the stronger lower bound. -/
theorem eight_mul_divisors_le_of_no_four
    {G B E C : Type*} [Group G] [Group B] [Group E] [Group C]
    [Fintype G] [Fintype B] [Fintype E] [Fintype C] [IsCyclic C]
    (hBcard : Nat.card B = 8) (hEcard : Nat.card E = 8)
    (hB : ∀ b : B, b ^ 4 = 1) (hE : ∀ e : E, e ^ 2 = 1)
    (hC : Odd (Nat.card C)) (hG : ∀ g : G, ¬ 4 ∣ orderOf g)
    (f : G ≃ B × C) (hf : ∀ g : G, orderOf g ∣ orderOf (f g)) :
    8 * (Nat.card C).divisors.card ≤ cyc G := by
  obtain ⟨e, he⟩ := exists_order_dvd_equiv_of_no_four (hBcard.trans hEcard.symm) hB hE hC hG f hf
  have hco : (Nat.card E).Coprime (Nat.card C) := by
    rw [hEcard]
    simpa using hC.coprime_two_left.pow_left 3
  have hcount : cyc (E × C) = 8 * (Nat.card C).divisors.card := by
    change Nat.card (CyclicSum.CyclicSubgroups (E × C)) = _
    rw [CyclicSum.cyclic_count_prod_of_coprime hco,
      CyclicSum.cyclic_count_eq_card_of_exponent_two hE, hEcard,
      CyclicSum.cyclic_count_eq_divisors_card]
  rw [← hcount]
  exact CyclicSum.cyclic_count_le_of_order_dvd_equiv e he

#print axioms dvd_two_mul_of_dvd_four_mul
#print axioms exists_order_dvd_equiv_of_no_four
#print axioms eight_mul_divisors_le_of_no_four
end
end ElementaryCollapse



namespace CyclicSum

/-- If a Sylow 2-subgroup has exponent dividing 2, then no group element
has order divisible by 4. -/
theorem not_four_dvd_orderOf_of_sylow_exponent_two
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hP : ∀ x : P, x ^ 2 = 1) (g : G) : ¬ 4 ∣ orderOf g := by
  classical
  intro hg
  let x : G := g ^ (orderOf g / 4)
  have hx : orderOf x = 4 :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hg
  have hX : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers, hx]
    norm_num
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  let y : Q := ⟨x, hQ (Subgroup.mem_zpowers x)⟩
  let e : Q ≃* P := Q.equiv P
  have hy : y ^ 2 = 1 := by
    apply e.injective
    simpa using hP (e y)
  have hx2 : x ^ 2 = 1 := congrArg (fun z : Q => (z : G)) hy
  have hdiv : (4 : ℕ) ∣ 2 := by
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one hx2
  norm_num at hdiv

#print axioms not_four_dvd_orderOf_of_sylow_exponent_two
end CyclicSum


namespace ElementaryBound
open TwoFactor
noncomputable section

abbrev E3 := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)

lemma card_E3 : Nat.card E3 = 8 := by
  simp [E3]

lemma exponent_E3 (e : E3) : e ^ 2 = 1 := by
  change (2 : ℕ) • Multiplicative.toAdd e = 0
  ext <;> simp [nsmul_eq_mul, show (2 : ZMod 2) = 0 by decide]

/-- The elementary-Sylow branch contradicts the conjectured strict bound
once the comparison bijection is supplied. -/
theorem lower_bound_of_sylow_exponent_two_comparison
    {G B C : Type*} [Group G] [Group B] [Group C]
    [Fintype G] [Fintype B] [Fintype C] [IsCyclic C]
    (P : Sylow 2 G) (hP : ∀ x : P, x ^ 2 = 1)
    (hBcard : Nat.card B = 8) (hB : ∀ b : B, b ^ 4 = 1)
    (hC : Odd (Nat.card C))
    (f : G ≃ B × C) (hf : ∀ g : G, orderOf g ∣ orderOf (f g)) :
    2 ^ ((Nat.card G).primeFactors.card + 2) ≤ cyc G := by
  have hcount := ElementaryCollapse.eight_mul_divisors_le_of_no_four
    (E := E3) hBcard card_E3 hB exponent_E3 hC
    (CyclicSum.not_four_dvd_orderOf_of_sylow_exponent_two P hP) f hf
  have hcardG : Nat.card G = 2 ^ 3 * Nat.card C := by
    rw [Nat.card_congr f, Nat.card_prod, hBcard]
    norm_num
  have hnotdiv : ¬ 2 ∣ Nat.card C := by
    simpa only [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hC)
  have hprime : (Nat.card G).primeFactors.card = (Nat.card C).primeFactors.card + 1 := by
    rw [hcardG]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 3 _ Nat.prime_two (by omega)
      Nat.card_pos hnotdiv
  rw [hprime, show (Nat.card C).primeFactors.card + 1 + 2 =
    (Nat.card C).primeFactors.card + 3 by omega, pow_add]
  have hτ := two_pow_card_primeFactors_le_card_divisors (Nat.card C) Nat.card_pos
  calc
    _ = 8 * 2 ^ (Nat.card C).primeFactors.card := by ring
    _ ≤ 8 * (Nat.card C).divisors.card := Nat.mul_le_mul_left 8 hτ
    _ ≤ cyc G := hcount

#print axioms card_E3
#print axioms exponent_E3
#print axioms lower_bound_of_sylow_exponent_two_comparison
end
end ElementaryBound



namespace Conjecture55C4C2

abbrev A := ZMod 4 × ZMod 2

def e₁ : A := (1, 0)
def e₂ : A := (0, 1)

def generatorMap (a b x : A) : A := x.1.val • a + x.2.val • b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Only the images of two generators are enumerated, not all permutations. -/
theorem generatorMap_fourth :
    ∀ a b : A, (2 : ℕ) • a ≠ 0 → (2 : ℕ) • b = 0 → b ≠ 0 → b ≠ (2 : ℕ) • a →
      ∀ x : A, generatorMap a b (generatorMap a b (generatorMap a b (generatorMap a b x))) = x := by
  decide

/-- Every additive automorphism of C₄ × C₂ has fourth power equal to identity. -/
theorem addAut_apply_four (f : AddAut A) (x : A) : f (f (f (f x))) = x := by
  have hrep (y : A) : f y = generatorMap (f e₁) (f e₂) y := by
    have hy : y = y.1.val • e₁ + y.2.val • e₂ := by
      ext <;> simp [e₁, e₂, nsmul_eq_mul]
    calc
      f y = f (y.1.val • e₁ + y.2.val • e₂) := congrArg f hy
      _ = generatorMap (f e₁) (f e₂) y := by
        unfold generatorMap
        rw [map_add, map_nsmul, map_nsmul]
  have ha : (2 : ℕ) • f e₁ ≠ 0 := by
    have h := f.injective.ne (show (2 : ℕ) • e₁ ≠ 0 by decide)
    simpa only [map_nsmul, map_zero] using h
  have hb : (2 : ℕ) • f e₂ = 0 := by
    rw [← map_nsmul, show (2 : ℕ) • e₂ = 0 by decide, map_zero]
  have hb0 : f e₂ ≠ 0 := by
    have h := f.injective.ne (show e₂ ≠ 0 by decide)
    simpa only [map_zero] using h
  have hba : f e₂ ≠ (2 : ℕ) • f e₁ := by
    have h := f.injective.ne (show e₂ ≠ (2 : ℕ) • e₁ by decide)
    simpa only [map_nsmul] using h
  let a := f e₁
  let b := f e₂
  have hfun : (f : A → A) = generatorMap a b := funext hrep
  change (f : A → A) ((f : A → A) ((f : A → A) ((f : A → A) x))) = x
  rw [hfun]
  exact generatorMap_fourth a b ha hb hb0 hba x

/-- Multiplicative form used by the Sylow normal-complement criterion. -/
theorem mulAut_fourth (f : MulAut (Multiplicative A)) : f ^ 4 = 1 := by
  apply MulEquiv.ext
  intro x
  change f (f (f (f x))) = x
  exact addAut_apply_four (AddEquiv.toMultiplicative.symm f) x

/-- The automorphism group of C₄ × C₂ is a 2-group. -/
theorem isPGroup_mulAut : IsPGroup 2 (MulAut (Multiplicative A)) := by
  intro f
  exact ⟨2, by simpa using mulAut_fourth f⟩

/-- Transport the automorphism-group conclusion along a chosen group isomorphism. -/
theorem isPGroup_mulAut_of_equiv {G : Type*} [Group G]
    (e : G ≃* Multiplicative A) : IsPGroup 2 (MulAut G) :=
  isPGroup_mulAut.of_equiv (MulAut.congr e).symm

#print axioms isPGroup_mulAut_of_equiv
#print axioms mulAut_fourth
#print axioms isPGroup_mulAut
#print axioms generatorMap_fourth
#print axioms addAut_apply_four
open Subgroup



/-- A squarefree normal complement is a solvable Z-group. -/
theorem isSolvable_of_aut_isPGroup_of_squarefree_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsMulCommutative P]
    (hAut : IsPGroup p (MulAut P)) (hs : Squarefree P.index) : Group.IsSolvable G := by
  obtain ⟨N, hN, hcomp⟩ := SylowInputs.exists_normal_complement_of_aut_isPGroup P hAut
  let : N.Normal := hN
  have hcard : Nat.card N = P.index := hcomp.index_eq_card.symm
  let : IsZGroup N := IsZGroup.of_squarefree (hcard.symm ▸ hs)
  let : Group.IsSolvable P := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  have hQ : Group.IsSolvable (G ⧸ N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := hcomp.symm.QuotientMulEquiv.toMonoidHom) hcomp.symm.QuotientMulEquiv.injective
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, hQ⟩

/-- The C₄ × C₂ Sylow case with squarefree odd part is solvable.
This closes the concrete abelian order-eight branch of the proposed reduction. -/
theorem isSolvable_of_c4c2_sylow_of_squarefree_index
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (e : P ≃* Multiplicative A) (hs : Squarefree P.index) :
    Group.IsSolvable G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsMulCommutative P := IsMulCommutative.of_comm (fun x y => by
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _)
  exact isSolvable_of_aut_isPGroup_of_squarefree_index P (isPGroup_mulAut_of_equiv e) hs

#print axioms isSolvable_of_aut_isPGroup_of_squarefree_index
#print axioms isSolvable_of_c4c2_sylow_of_squarefree_index
end Conjecture55C4C2



namespace OrderShape

/-- The genuine comparison bijection and strict FC bound force the full
small-order shape, without any independent numerical count assumptions. -/
theorem order_shape_of_comparison
    {G K H : Type*} [Group G] [Group K] [Group H]
    [Fintype G] [Fintype K] [Fintype H] [IsCyclic K]
    (a m : ℕ) (ha : 2 ≤ a) (hm : Odd m)
    (hK : Nat.card K = 2 ^ (a - 1) * m) (hH : Nat.card H = 2)
    (e : G ≃ K × H) (he : ∀ x : G, orderOf x ∣ orderOf (e x))
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    (a = 2 ∧ (∀ p, m.factorization p ≤ 2) ∧
      ∀ p q, 2 ≤ m.factorization p → 2 ≤ m.factorization q → p = q) ∨
    (a = 3 ∧ Squarefree m) := by
  have ha1 : 1 ≤ a := by omega
  have hmpos : 0 < m := hm.pos
  have h2 : ¬ 2 ∣ m := by
    simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm
  have hpow : 2 ^ (a - 1) * 2 = 2 ^ a := by
    rw [← pow_succ]
    congr 1
    omega
  have hcard : Nat.card G = 2 ^ a * m := by
    rw [Nat.card_congr e, Nat.card_prod, hK, hH]
    calc
      2 ^ (a - 1) * m * 2 = (2 ^ (a - 1) * 2) * m := by ring
      _ = 2 ^ a * m := by rw [hpow]
  have hω : numPrimeFactors G = m.primeFactors.card + 1 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
    rw [hcard]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 a m Nat.prime_two ha1 hmpos h2
  have hcount := ComparisonModel.cyclic_count_lower_bound_of_comparison
    a m ha1 hm hK hH e he
  have hsmall : 2 * a * m.divisors.card < 2 ^ (numPrimeFactors G + 2) :=
    hcount.trans_lt hlt
  have ht : 1 ≤ numPrimeFactors G := by omega
  have hd : 2 ^ (numPrimeFactors G - 1) ≤ m.divisors.card := by
    rw [hω]
    simpa using two_pow_card_primeFactors_le_card_divisors m hmpos
  have hcases := two_part_exponent_restriction a m.divisors.card (numPrimeFactors G)
    ha ht hd hsmall
  have hsmall' : 2 * a * m.divisors.card < 8 * 2 ^ m.primeFactors.card := by
    have hexp : 2 ^ (numPrimeFactors G + 2) = 8 * 2 ^ m.primeFactors.card := by
      rw [hω, show m.primeFactors.card + 1 + 2 = m.primeFactors.card + 3 by omega,
        pow_add]
      ring
    rwa [hexp] at hsmall
  rcases hcases with hA | hA
  · left
    refine ⟨hA, ?_⟩
    apply factorization_shape_of_four_mul_card_divisors_lt m hmpos
    simpa [hA] using hsmall'
  · right
    refine ⟨hA, ?_⟩
    apply squarefree_of_six_mul_card_divisors_lt m hmpos
    simpa [hA] using hsmall'

#print axioms order_shape_of_comparison
end OrderShape


namespace PrimePower

/-- An odd fourth power is one modulo sixteen. -/
theorem odd_fourth_mod_sixteen (p : ℕ) (hp : Odd p) : p ^ 4 % 16 = 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hp
  rw [Nat.pow_mod]
  have hlt : p % 16 < 16 := Nat.mod_lt _ (by omega)
  interval_cases h : p % 16 <;> omega

/-- An odd square parameter makes the PSL₂ order a multiple of eight. -/
theorem eight_dvd_order_at_odd_square (p s : ℕ) (hp : Odd p)
    (hs : 2 * s = p ^ 2 * ((p ^ 2) ^ 2 - 1)) : 8 ∣ s := by
  have hmod := odd_fourth_mod_sixteen p hp
  have h16 : 16 ∣ (p ^ 2) ^ 2 - 1 := by
    rw [← pow_mul]
    norm_num only [Nat.reduceMul]
    omega
  have h16s : 16 ∣ 2 * s := hs ▸ dvd_mul_of_dvd_right h16 (p ^ 2)
  omega

/-- The defining prime-power divisor survives removing the two-part of an
ambient order. The equality is the doubled numerical PSL₂ order formula. -/
theorem prime_power_dvd_odd_part (p f a m s : ℕ) (hp : Odd p)
    (hs : 2 * s = p ^ f * ((p ^ f) ^ 2 - 1))
    (hdiv : s ∣ 2 ^ a * m) : p ^ f ∣ m := by
  have hc : (p ^ f).Coprime 2 := hp.coprime_two_right.pow_left f
  have hpf : p ^ f ∣ 2 * s := hs ▸ dvd_mul_right (p ^ f) _
  have hps : p ^ f ∣ s := hc.dvd_of_dvd_mul_left hpf
  exact (hc.pow_right a).dvd_of_dvd_mul_left (hps.trans hdiv)

/-- The small-order shape forces an odd prime-power PSL₂ parameter to be prime.
The a=2 case needs only the individual exponent bounds, not uniqueness of
an exponent-two prime. -/
theorem exponent_eq_one_of_order_dvd_small_shape
    (p f a m s : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hm : Odd m)
    (hs : 2 * s = p ^ f * ((p ^ f) ^ 2 - 1))
    (hdiv : s ∣ 2 ^ a * m)
    (hshape : (a = 2 ∧ ∀ r, m.factorization r ≤ 2) ∨ (a = 3 ∧ Squarefree m)) :
    f = 1 := by
  have hpm : p ^ f ∣ m := prime_power_dvd_odd_part p f a m s hpodd hs hdiv
  have hle : f ≤ m.factorization p := (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hm.pos)).mp hpm
  rcases hshape with ⟨ha, hshape⟩ | ⟨ha, hshape⟩
  · have hf2 : f ≤ 2 := hle.trans (hshape p)
    by_contra hf1
    have hfeq : f = 2 := by omega
    have h8 : 8 ∣ s := eight_dvd_order_at_odd_square p s hpodd (by simpa [hfeq] using hs)
    have h8m : 8 ∣ 4 * m := by simpa [ha] using h8.trans hdiv
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  · have hle1 := hshape.natFactorization_le_one p
    omega

/-- Direct formulation using the actual numerical order, with no separate
hypothesis for the doubled order formula. -/
theorem exponent_eq_one_of_psl2_order_dvd_small_shape
    (p f a m : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hm : Odd m)
    (hdiv : p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∣ 2 ^ a * m)
    (hshape : (a = 2 ∧ ∀ r, m.factorization r ≤ 2) ∨ (a = 3 ∧ Squarefree m)) :
    f = 1 := by
  have hoddSq : Odd ((p ^ f) ^ 2) := hpodd.pow.pow
  have htwo : 2 ∣ (p ^ f) ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hoddSq
    omega
  have htwoProd : 2 ∣ p ^ f * ((p ^ f) ^ 2 - 1) := dvd_mul_of_dvd_right htwo _
  apply exponent_eq_one_of_order_dvd_small_shape p f a m _ hp hpodd hf hm ?_ hdiv hshape
  simpa [Nat.mul_comm] using Nat.div_mul_cancel htwoProd

#print axioms odd_fourth_mod_sixteen
#print axioms eight_dvd_order_at_odd_square
#print axioms prime_power_dvd_odd_part
#print axioms exponent_eq_one_of_order_dvd_small_shape
#print axioms exponent_eq_one_of_psl2_order_dvd_small_shape
end PrimePower


namespace AlternatingSeven

theorem order_not_dvd_small_shape (a m : ℕ) (hm : Odd m)
    (hshape : a = 2 ∨ (a = 3 ∧ Squarefree m)) :
    ¬ 2520 ∣ 2 ^ a * m := by
  intro hdiv
  rcases hshape with ha | ⟨ha, hsf⟩
  · have h8 : 8 ∣ 4 * m := by
      have := (show 8 ∣ 2520 by norm_num).trans hdiv
      simpa [ha] using this
    have hodd := Nat.odd_iff.mp hm
    omega
  · have h9 : 9 ∣ 8 * m := by
      have := (show 9 ∣ 2520 by norm_num).trans hdiv
      simpa [ha] using this
    have h9m : 9 ∣ m := (show Nat.Coprime 9 8 by decide).dvd_of_dvd_mul_left h9
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf) 3 (by norm_num) h9m

theorem card_a7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num

theorem no_embedding_of_small_shape {G : Type*} [Group G] [Finite G]
    (a m : ℕ) (hm : Odd m) (hcard : Nat.card G = 2 ^ a * m)
    (hshape : a = 2 ∨ (a = 3 ∧ Squarefree m))
    (f : alternatingGroup (Fin 7) →* G) : ¬ Function.Injective f := by
  intro hf
  have hd := Subgroup.card_dvd_of_injective f hf
  rw [card_a7, hcard] at hd
  exact order_not_dvd_small_shape a m hm hshape hd

#print axioms order_not_dvd_small_shape
#print axioms card_a7
#print axioms no_embedding_of_small_shape
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
#print axioms conjecture55_iff_lower_bound
#print axioms cyclicSubgroupMap
#print axioms cyclicSubgroupMap_injective
#print axioms cyclicSubgroupMap_surjective
#print axioms cyc_le_of_injective
#print axioms cyc_le_of_surjective
#print axioms cyc_eq_of_mulEquiv
#print axioms lower_bound_of_embedding
#print axioms cyc_quotient_le
#print axioms lower_bound_after_doubling
#print axioms two_part_exponent_restriction
#print axioms a5_count_arithmetic
#print axioms j1_count_arithmetic
#print axioms psl2_count_sum
#print axioms psl2_final_arithmetic
#print axioms affirmative_target_of_lower_bound

end

end Conjecture55Lean4Web
