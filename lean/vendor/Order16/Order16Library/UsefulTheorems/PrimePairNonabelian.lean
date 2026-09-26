/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.PrimeOrderClassification
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Nat.Prime.Int

/-!
# The non-abelian group of order `p * q`

When `q ∣ p - 1` there is, besides the cyclic group, a non-abelian group of order `p * q`: the
semidirect product `ℤ/p ⋊ ℤ/q` for a non-trivial action of `ℤ/q` on `ℤ/p`.

## Main results

* `NonabRep c hc = ℤ/p ⋊ ℤ/q` (action by a unit `c` of order `q`), with `card_nonabRep`
  (order `p·q`), `not_isCyclic_nonabRep` (non-abelian when `c ≠ 1`), and
  `cyclicRep_not_mulEquiv_nonabRep` (distinct from the cyclic group).
* `exists_unit_orderOf_eq` — a unit of order `q` exists when `q ∣ p - 1`.
* `nonempty_mulEquiv_nonabRep` — the heart of exhaustiveness: a finite group with an element of
  order `p`, an element of order `q`, and the conjugation relation `b a b⁻¹ = a^c` is isomorphic to
  `NonabRep c hc` (isomorphism via `SemidirectProduct.lift`; injectivity + cardinality).
* `exists_generators_of_card_eq_prime_mul` — the Sylow setup: a non-cyclic group of order `p·q` has
  such generators (Sylow-`p` is normal, an order-`q` element exists, conjugation gives the unit).
* `unit_mem_zpowers_of_pow_eq` — relabelling: a `q`-th root of unity lies in the order-`q` subgroup.
* **`classification_card_eq_prime_mul`** (and `…'`) — the full classification: for a fixed order-`q`
  unit `c₀`, every group of order `p·q` is cyclic or isomorphic to `NonabRep c₀`.
-/

namespace Smallgroups.UsefulTheorems

/-- If `gⁿ = 1`, then `g ^ (·).val : ZMod n → M` turns addition into multiplication. -/
theorem pow_val_add {M : Type*} [Group M] {g : M} {n : ℕ} [NeZero n] (hg : g ^ n = 1)
    (i j : ZMod n) : g ^ (i + j).val = g ^ i.val * g ^ j.val := by
  rw [← pow_add]
  apply pow_eq_pow_iff_modEq.mpr
  refine Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hg) ?_
  rw [ZMod.val_add]
  exact Nat.mod_modEq _ _

variable {p : ℕ}

/-- Multiplication by a unit of `ZMod p`, as an automorphism of the multiplicative group
`Multiplicative (ZMod p)`. Packaged as a group hom from `(ZMod p)ˣ`. -/
noncomputable def unitAutHom : (ZMod p)ˣ →* MulAut (Multiplicative (ZMod p)) where
  toFun u := AddEquiv.toMultiplicative (DistribMulAction.toAddEquiv (ZMod p) u)
  map_one' := by ext m; simp
  map_mul' u v := by ext m; simp [mul_smul]

@[simp] theorem unitAutHom_apply (u : (ZMod p)ˣ) (m : ZMod p) :
    unitAutHom u (Multiplicative.ofAdd m) = Multiplicative.ofAdd ((u : ZMod p) * m) := by
  simp [unitAutHom, Units.smul_def]

/-- Multiplication by units embeds into the automorphism group of the additive cyclic group
`ZMod p`, written multiplicatively. -/
theorem unitAutHom_injective [Fact p.Prime] : Function.Injective (unitAutHom (p := p)) := by
  intro u v h
  have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod p)) =
      unitAutHom v (Multiplicative.ofAdd (1 : ZMod p)) := by rw [h]
  simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
  exact Units.ext (congrArg Multiplicative.toAdd h1)

/-- Every automorphism of the cyclic group `ZMod p` is multiplication by a unit. -/
theorem exists_unitAutHom_eq [Fact p.Prime] (σ : MulAut (Multiplicative (ZMod p))) :
    ∃ u : (ZMod p)ˣ, σ = unitAutHom u := by
  let u_val : ZMod p := (σ (Multiplicative.ofAdd (1 : ZMod p))).toAdd
  have hu_ne_zero : u_val ≠ 0 := by
    intro hz
    have h0 : σ (Multiplicative.ofAdd (0 : ZMod p)) = Multiplicative.ofAdd (0 : ZMod p) := by
      calc
        σ (Multiplicative.ofAdd (0 : ZMod p)) = σ 1 := by simp
        _ = 1 := map_one σ
        _ = Multiplicative.ofAdd (0 : ZMod p) := by simp
    have h1 : σ (Multiplicative.ofAdd (1 : ZMod p)) = Multiplicative.ofAdd (0 : ZMod p) := by
      calc
        σ (Multiplicative.ofAdd (1 : ZMod p)) = Multiplicative.ofAdd u_val := rfl
        _ = Multiplicative.ofAdd (0 : ZMod p) := by rw [hz]
    have h01 : Multiplicative.ofAdd (0 : ZMod p) ≠ Multiplicative.ofAdd (1 : ZMod p) := by
      intro h
      apply_fun Multiplicative.toAdd at h
      simp at h
    apply h01
    exact σ.injective (h0.trans h1.symm)
  have h_inv : u_val⁻¹ * u_val = 1 := by field_simp [hu_ne_zero]
  have h_mul : u_val * u_val⁻¹ = 1 := by field_simp [hu_ne_zero]
  let u : (ZMod p)ˣ := Units.mk u_val (u_val⁻¹) h_mul h_inv
  refine ⟨u, ?_⟩
  apply MulEquiv.ext
  intro x
  let n := Multiplicative.toAdd x
  have hx : Multiplicative.ofAdd n = x := by
    exact ofAdd_toAdd x
  rw [← hx]
  calc
    σ (Multiplicative.ofAdd n) = σ ((Multiplicative.ofAdd (1 : ZMod p)) ^ n.val) := by
      rw [show (Multiplicative.ofAdd n : Multiplicative (ZMod p)) =
          (Multiplicative.ofAdd (1 : ZMod p)) ^ n.val from by
        calc
          Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod p)) := by
            rw [ZMod.natCast_zmod_val]
          _ = Multiplicative.ofAdd (n.val • (1 : ZMod p)) := by simp
          _ = (Multiplicative.ofAdd (1 : ZMod p)) ^ n.val := by
            rw [ofAdd_nsmul]
      ]
    _ = (σ (Multiplicative.ofAdd (1 : ZMod p))) ^ n.val := by rw [map_pow]
    _ = (Multiplicative.ofAdd u_val) ^ n.val := rfl
    _ = Multiplicative.ofAdd (n.val • u_val) := by
      rw [← ofAdd_nsmul]
    _ = Multiplicative.ofAdd (u_val * (n.val : ZMod p)) := by
      rw [nsmul_eq_mul, mul_comm]
    _ = Multiplicative.ofAdd (u_val * n) := by rw [ZMod.natCast_zmod_val]
    _ = unitAutHom u (Multiplicative.ofAdd n) := by
      rw [unitAutHom_apply]

variable {q : ℕ}

/-- The hom `Multiplicative (ZMod q) →* (ZMod p)ˣ` sending the generator to a unit `c` with
`c ^ q = 1`. -/
noncomputable def powHom [NeZero q] (c : (ZMod p)ˣ) (hc : c ^ q = 1) :
    Multiplicative (ZMod q) →* (ZMod p)ˣ :=
  MonoidHom.mk' (fun x => c ^ (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add hc (Multiplicative.toAdd a) (Multiplicative.toAdd b))

/-- The action of `ℤ/q` on `ℤ/p` by multiplication by `c` (a unit of order dividing `q`). -/
noncomputable def actionHom [NeZero q] (c : (ZMod p)ˣ) (hc : c ^ q = 1) :
    Multiplicative (ZMod q) →* MulAut (Multiplicative (ZMod p)) :=
  unitAutHom.comp (powHom c hc)

/-- The non-abelian representative of order `p * q`: the semidirect product `ℤ/p ⋊ ℤ/q`. -/
noncomputable abbrev NonabRep [NeZero q] (c : (ZMod p)ˣ) (hc : c ^ q = 1) : Type :=
  Multiplicative (ZMod p) ⋊[actionHom c hc] Multiplicative (ZMod q)

@[simp] theorem actionHom_apply [NeZero q] (c : (ZMod p)ˣ) (hc : c ^ q = 1) (j : ZMod q)
    (m : ZMod p) : actionHom c hc (Multiplicative.ofAdd j) (Multiplicative.ofAdd m)
      = Multiplicative.ofAdd (((c ^ j.val : (ZMod p)ˣ) : ZMod p) * m) := by
  have hpow : powHom c hc (Multiplicative.ofAdd j) = c ^ j.val := rfl
  change unitAutHom (powHom c hc (Multiplicative.ofAdd j)) (Multiplicative.ofAdd m) = _
  rw [hpow, unitAutHom_apply]

/-- The representative has order `p * q`. -/
theorem card_nonabRep [NeZero p] [NeZero q] (c : (ZMod p)ˣ) (hc : c ^ q = 1) :
    Nat.card (NonabRep c hc) = p * q := by
  rw [NonabRep, SemidirectProduct.card]
  change Nat.card (CyclicRep p) * Nat.card (CyclicRep q) = p * q
  rw [card_cyclicRep (NeZero.ne p), card_cyclicRep (NeZero.ne q)]

/-- For a non-trivial action (`c ≠ 1`) the representative is **not cyclic**: the generators of the
two factors do not commute. -/
theorem not_isCyclic_nonabRep [NeZero p] [NeZero q] (hq : 1 < q)
    (c : (ZMod p)ˣ) (hc : c ^ q = 1) (hc1 : c ≠ 1) : ¬ IsCyclic (NonabRep c hc) := by
  haveI : Fact (1 < q) := ⟨hq⟩
  intro hcyc
  letI := hcyc.commGroup
  have hfix : actionHom c hc (Multiplicative.ofAdd (1 : ZMod q))
      (Multiplicative.ofAdd (1 : ZMod p)) = Multiplicative.ofAdd (1 : ZMod p) := by
    have hcomm : (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod q)) : NonabRep c hc)
          * SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod p))
        = SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod p))
          * SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod q)) := mul_comm _ _
    have heq : (SemidirectProduct.inl (actionHom c hc (Multiplicative.ofAdd (1 : ZMod q))
          (Multiplicative.ofAdd (1 : ZMod p))) : NonabRep c hc)
        = SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod p)) := by
      rw [SemidirectProduct.inl_aut, hcomm, mul_assoc, ← map_mul, mul_inv_cancel]
      simp
    exact SemidirectProduct.inl_injective heq
  rw [actionHom_apply, ZMod.val_one, pow_one, mul_one] at hfix
  exact hc1 (Units.val_eq_one.mp (Multiplicative.ofAdd.injective hfix))

/-- For a non-trivial action (`c ≠ 1`) the representative is **not commutative**. -/
theorem nonabRep_not_comm [NeZero p] [NeZero q] (hq : 1 < q)
    (c : (ZMod p)ˣ) (hc : c ^ q = 1) (hc1 : c ≠ 1) :
    ¬ ∀ a b : NonabRep c hc, a * b = b * a := by
  haveI : Fact (1 < q) := ⟨hq⟩
  intro hcomm
  have hfix : actionHom c hc (Multiplicative.ofAdd (1 : ZMod q))
      (Multiplicative.ofAdd (1 : ZMod p)) = Multiplicative.ofAdd (1 : ZMod p) := by
    have h := hcomm (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod q)))
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod p)))
    have heq : (SemidirectProduct.inl (actionHom c hc (Multiplicative.ofAdd (1 : ZMod q))
          (Multiplicative.ofAdd (1 : ZMod p))) : NonabRep c hc)
        = SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod p)) := by
      rw [SemidirectProduct.inl_aut, h, mul_assoc, ← map_mul, mul_inv_cancel]
      simp
    exact SemidirectProduct.inl_injective heq
  rw [actionHom_apply, ZMod.val_one, pow_one, mul_one] at hfix
  exact hc1 (Units.val_eq_one.mp (Multiplicative.ofAdd.injective hfix))

/-- **Distinctness.** The cyclic group of order `p * q` is not isomorphic to the non-abelian
representative (the latter is not cyclic). -/
theorem cyclicRep_not_mulEquiv_nonabRep [NeZero p] [NeZero q] (hq : 1 < q)
    (c : (ZMod p)ˣ) (hc : c ^ q = 1) (hc1 : c ≠ 1) :
    ¬ Nonempty (CyclicRep (p * q) ≃* NonabRep c hc) := by
  rintro ⟨e⟩
  exact not_isCyclic_nonabRep hq c hc hc1 (e.isCyclic.mp inferInstance)

/-- Since `q ∣ p - 1 = |(ZMod p)ˣ|` and `(ZMod p)ˣ` is cyclic, there is a unit of order `q`. -/
theorem exists_unit_orderOf_eq {q : ℕ} (hp : p.Prime) (hdvd : q ∣ p - 1) :
    ∃ c : (ZMod p)ˣ, orderOf c = q ∧ c ^ q = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  rw [hcard] at hg
  have hne : orderOf g ≠ 0 := by rw [hg]; have := hp.two_le; omega
  have hqd : q ∣ orderOf g := hg ▸ hdvd
  refine ⟨g ^ (orderOf g / q), orderOf_pow_orderOf_div hne hqd, ?_⟩
  have h := pow_orderOf_eq_one (g ^ (orderOf g / q))
  rwa [orderOf_pow_orderOf_div hne hqd] at h

/-- In the cyclic group `(ZMod p)ˣ`, any `q`-th root of unity lies in the subgroup generated by an
element of order `q` (both are the unique order-`q` subgroup). -/
theorem unit_mem_zpowers_of_pow_eq {q : ℕ} (hp : p.Prime) (hq : 0 < q)
    (c c₀ : (ZMod p)ˣ) (hc : orderOf c = q) (hc₀ : c₀ ^ q = 1) :
    c₀ ∈ Subgroup.zpowers c := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  classical
  have hcq : c ^ q = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hsub : (Subgroup.zpowers c : Set (ZMod p)ˣ).toFinset ⊆
      Finset.univ.filter (· ^ q = 1) := by
    intro x hx
    rw [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨j, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcq, one_zpow]
  have hcard_z : (Subgroup.zpowers c : Set (ZMod p)ˣ).toFinset.card = q := by
    rw [Set.toFinset_card]
    exact (Nat.card_eq_fintype_card.symm.trans (Nat.card_zpowers c)).trans hc
  have heq : (Subgroup.zpowers c : Set (ZMod p)ˣ).toFinset = Finset.univ.filter (· ^ q = 1) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard_z]; exact IsCyclic.card_pow_eq_one_le hq)
  have hmem : c₀ ∈ Finset.univ.filter (· ^ q = 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc₀]
  rw [← heq, Set.mem_toFinset, SetLike.mem_coe] at hmem
  exact hmem

/-! ### Exhaustiveness: a group with the right generators is the representative -/

variable {G : Type*} [Group G]

/-- **Core of exhaustiveness.** A finite group `G` of order `p * q` containing an element `a` of
order `p` and an element `b` of order `q` with `b a b⁻¹ = a^c` (for a unit `c` of `ZMod p` with
`c^q = 1`) is isomorphic to the representative `NonabRep c hc`. -/
theorem nonempty_mulEquiv_nonabRep [NeZero p] [NeZero q] [Finite G]
    (a b : G) (ha : orderOf a = p) (hb : orderOf b = q)
    (c : (ZMod p)ˣ) (hc : c ^ q = 1) (hconj : b * a * b⁻¹ = a ^ (c : ZMod p).val)
    (hcoprime : Nat.Coprime p q) (hcard : Nat.card G = p * q) :
    Nonempty (G ≃* NonabRep c hc) := by
  haveI : Fintype G := Fintype.ofFinite G
  have hap : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hbq : b ^ q = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  -- the two factor homomorphisms
  let fn : Multiplicative (ZMod p) →* G :=
    MonoidHom.mk' (fun x => a ^ (Multiplicative.toAdd x).val) (fun x y => pow_val_add hap _ _)
  let fg : Multiplicative (ZMod q) →* G :=
    MonoidHom.mk' (fun x => b ^ (Multiplicative.toAdd x).val) (fun x y => pow_val_add hbq _ _)
  have fn_apply : ∀ m : ZMod p, fn (Multiplicative.ofAdd m) = a ^ m.val := fun _ => rfl
  have fg_apply : ∀ m : ZMod q, fg (Multiplicative.ofAdd m) = b ^ m.val := fun _ => rfl
  -- conjugation of `a^m` by `b`
  have hconj_a : ∀ m : ℕ, b * a ^ m * b⁻¹ = a ^ ((c : ZMod p).val * m) := by
    intro m; rw [← conj_pow, hconj, ← pow_mul]
  -- conjugation of `fn x` by `b` realises `unitAutHom c`
  have hconj1 : ∀ x, b * fn x * b⁻¹ = fn (unitAutHom c x) := by
    intro x
    have hx : unitAutHom c x = Multiplicative.ofAdd ((c : ZMod p) * x.toAdd) :=
      unitAutHom_apply c x.toAdd
    rw [hx, fn_apply]
    change b * a ^ (x.toAdd).val * b⁻¹ = a ^ ((c : ZMod p) * x.toAdd).val
    rw [hconj_a]
    apply pow_eq_pow_iff_modEq.mpr
    rw [ha, ZMod.val_mul]
    exact (Nat.mod_modEq _ _).symm
  have hmulAut : ∀ (u v : (ZMod p)ˣ) (y), unitAutHom u (unitAutHom v y) = unitAutHom (u * v) y := by
    intro u v y; rw [map_mul]; rfl
  -- iterate: conjugation by `b^k` realises `unitAutHom (c^k)`
  have hconjk : ∀ (k : ℕ) (x), b ^ k * fn x * (b ^ k)⁻¹ = fn (unitAutHom (c ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      have hsplit : b ^ (n + 1) * fn x * (b ^ (n + 1))⁻¹
          = b ^ n * (b * fn x * b⁻¹) * (b ^ n)⁻¹ := by rw [pow_succ, mul_inv_rev]; group
      rw [hsplit, hconj1, ih, hmulAut, ← pow_succ]
  -- assemble the homomorphism out of the semidirect product
  let f : NonabRep c hc →* G := SemidirectProduct.lift fn fg (by
    intro g
    apply MonoidHom.ext
    intro x
    change fn (actionHom c hc g x) = fg g * fn x * (fg g)⁻¹
    have hg : actionHom c hc g x = unitAutHom (c ^ (Multiplicative.toAdd g).val) x := rfl
    rw [hg, ← hconjk]
    rfl)
  -- `f` is injective
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨n, g⟩ := x
    have hfx : fn n * fg g = 1 := hx
    set kg := (Multiplicative.toAdd g).val with hkg
    have hmem : b ^ kg ∈ Subgroup.zpowers a := by
      have hfgi : fg g = (fn n)⁻¹ := eq_inv_of_mul_eq_one_right hfx
      rw [show fg g = b ^ kg from rfl] at hfgi
      rw [hfgi]
      exact inv_mem (pow_mem (Subgroup.mem_zpowers a) (Multiplicative.toAdd n).val)
    have hbk_p : orderOf (b ^ kg) ∣ p := by
      have h := orderOf_dvd_natCard (⟨b ^ kg, hmem⟩ : Subgroup.zpowers a)
      rwa [Nat.card_zpowers, ha, Subgroup.orderOf_mk] at h
    have hbk_q : orderOf (b ^ kg) ∣ q := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hbq, one_pow]
    have hbk1 : b ^ kg = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcoprime hbk_p hbk_q)
    have hg1 : g = 1 := by
      have hqdvd : q ∣ kg := by
        have h := orderOf_dvd_of_pow_eq_one hbk1; rwa [hb] at h
      have hk0 : Multiplicative.toAdd g = 0 :=
        (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hqdvd (ZMod.val_lt _))
      apply Multiplicative.toAdd.injective; rw [hk0]; rfl
    have hn1 : n = 1 := by
      rw [hg1, map_one, mul_one] at hfx
      have hfx' : a ^ (Multiplicative.toAdd n).val = 1 := hfx
      have hpdvd : p ∣ (Multiplicative.toAdd n).val := by
        have h := orderOf_dvd_of_pow_eq_one hfx'; rwa [ha] at h
      have hn0 : Multiplicative.toAdd n = 0 :=
        (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hpdvd (ZMod.val_lt _))
      apply Multiplicative.toAdd.injective; rw [hn0]; rfl
    rw [hn1, hg1]; rfl
  -- injective + equal cardinality ⟹ bijective
  haveI : Finite (NonabRep c hc) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI : Fintype (NonabRep c hc) := Fintype.ofFinite _
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_nonabRep, hcard]⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

/-- **Setup for exhaustiveness.** A non-cyclic group of order `p * q` (`q < p` primes) has an
element `a` of order `p`, an element `b` of order `q`, and a unit `c ≠ 1` of order dividing `q` with
`b a b⁻¹ = a^c`. -/
theorem exists_generators_of_card_eq_prime_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) {G : Type*} [Group G] (hG : Nat.card G = p * q) (hncyc : ¬ IsCyclic G) :
    ∃ (a b : G) (c : (ZMod p)ˣ), orderOf a = p ∧ orderOf b = q ∧ c ^ q = 1 ∧ c ≠ 1 ∧
      b * a * b⁻¹ = a ^ (c : ZMod p).val := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  haveI : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact Nat.mul_ne_zero hp.pos.ne' hq.pos.ne')
  have hcoprime : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p (G := G) ⟨q, by rw [hG]⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' q (G := G) ⟨p, by rw [hG, Nat.mul_comm]⟩
  have hap : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  -- `⟨a⟩` is the unique (hence normal) Sylow `p`-subgroup.
  have hzacard : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hnp : Nat.card (Sylow p G) = 1 := by
    obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
    have hdvd : Nat.card (Sylow p G) ∣ p * q :=
      hG ▸ (P0.card_dvd_index.trans (Subgroup.index_dvd_card _))
    have hndvd : ¬ p ∣ Nat.card (Sylow p G) := not_dvd_card_sylow p G
    have hdq : Nat.card (Sylow p G) ∣ q :=
      Nat.Coprime.dvd_of_dvd_mul_left ((hp.coprime_iff_not_dvd.mpr hndvd).symm) hdvd
    rcases (Nat.dvd_prime hq).mp hdq with h | h
    · exact h
    · exfalso
      have hmod := card_sylow_modEq_one p G
      rw [h] at hmod
      have hd : p ∣ q - 1 := (Nat.modEq_iff_dvd' (by have := hq.two_le; omega)).mp hmod.symm
      have := Nat.le_of_dvd (by have := hq.two_le; omega) hd
      omega
  haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hnp).1
  have hpg : IsPGroup p (Subgroup.zpowers a) := by
    rw [IsPGroup.iff_card]; exact ⟨1, by rw [hzacard, pow_one]⟩
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup G) = p := by
    rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_mul hp.ne_zero hq.ne_zero]
    simp [hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd
      (fun h => hqp.ne' ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))]
  have hzaeq : Subgroup.zpowers a = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [hzacard, hQcard])
  haveI hzanorm : (Subgroup.zpowers a).Normal := hzaeq ▸ Sylow.normal_of_subsingleton Q
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- conjugation `b a b⁻¹ = a^k`, `k : ℤ`.
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzanorm.conj_mem a (Subgroup.mem_zpowers a) b)
  have ha1 : a ≠ 1 := by
    intro h; rw [h, orderOf_one] at ha; have := hp.two_le; omega
  -- the unit `c = (k : ZMod p)` (non-zero since `b a b⁻¹ ≠ 1`).
  have hbab1 : b * a * b⁻¹ ≠ 1 := fun h => ha1 (by
    have h2 : a = b⁻¹ * (b * a * b⁻¹) * b := by group
    rw [h] at h2; simpa using h2)
  have hkne : (k : ZMod p) ≠ 0 := by
    intro h0
    apply hbab1
    rw [← hk, zpow_eq_one_iff_modEq, ha, Int.modEq_zero_iff_dvd,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h0
  let c : (ZMod p)ˣ := Units.mk0 (k : ZMod p) hkne
  have hcval : (c : ZMod p) = (k : ZMod p) := rfl
  have hrel : b * a * b⁻¹ = a ^ (c : ZMod p).val := by
    rw [← hk, hcval, ← zpow_natCast a ((k : ZMod p).val), zpow_eq_zpow_iff_modEq, ha,
      show (((k : ZMod p).val : ℤ)) = k % (p : ℤ) from ZMod.val_intCast k]
    exact (Int.mod_modEq k p).symm
  -- conjugation by `b^j` raises to the power `c^j`.
  have hconj_iter : ∀ j : ℕ, b ^ j * a * (b ^ j)⁻¹ = a ^ (((c ^ j : (ZMod p)ˣ) : ZMod p)).val := by
    intro j
    induction j with
    | zero => simp [ZMod.val_one]
    | succ n ih =>
      have hsplit : b ^ (n + 1) * a * (b ^ (n + 1))⁻¹
          = b * (b ^ n * a * (b ^ n)⁻¹) * b⁻¹ := by rw [pow_succ, mul_inv_rev]; group
      rw [hsplit, ih, ← conj_pow, hrel, ← pow_mul]
      apply pow_eq_pow_iff_modEq.mpr
      rw [ha, show (((c ^ (n + 1) : (ZMod p)ˣ) : ZMod p)).val
            = ((c : ZMod p).val * (((c ^ n : (ZMod p)ˣ) : ZMod p)).val) % p from by
          rw [pow_succ', Units.val_mul, ZMod.val_mul]]
      exact (Nat.mod_modEq _ _).symm
  have hbq1 : b ^ q = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hcq : c ^ q = 1 := by
    have h1 : a ^ (((c ^ q : (ZMod p)ˣ) : ZMod p)).val = a ^ 1 := by
      rw [pow_one, ← hconj_iter q, hbq1]; group
    have hmod : (((c ^ q : (ZMod p)ˣ) : ZMod p)).val % p = 1 % p := by
      have := pow_eq_pow_iff_modEq.mp h1; rwa [ha] at this
      -- this : val ≡ 1 [MOD p]
    have hlt := ZMod.val_lt ((c ^ q : (ZMod p)ˣ) : ZMod p)
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp.one_lt] at hmod
    have : ((c ^ q : (ZMod p)ˣ) : ZMod p) = 1 := by
      have h := (ZMod.natCast_zmod_val ((c ^ q : (ZMod p)ˣ) : ZMod p)).symm
      rw [hmod] at h; simpa using h
    exact Units.ext this
  have hc1 : c ≠ 1 := by
    intro hc
    apply hncyc
    have hba : b * a * b⁻¹ = a := by rw [hrel, hc]; simp [ZMod.val_one]
    have hcomm : Commute a b := by
      have hcm : b * a = a * b := by
        calc b * a = b * a * b⁻¹ * b := by group
          _ = a * b := by rw [hba]
      exact hcm.symm
    have hord : orderOf (a * b) = p * q :=
      by rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hb]; exact hcoprime), ha, hb]
    exact isCyclic_of_orderOf_eq_card (a * b) (by rw [hord, hG])
  exact ⟨a, b, c, ha, hb, hcq, hc1, hrel⟩

/-- **Classification of groups of order `p * q` (`q ∣ p - 1`).** Given a fixed unit `c₀` of order
`q`, every group of order `p * q` is either cyclic or isomorphic to `NonabRep c₀`. -/
theorem classification_card_eq_prime_mul {p q : ℕ} [NeZero q] (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) {G : Type*} [Group G] (hG : Nat.card G = p * q)
    (c₀ : (ZMod p)ˣ) (hc₀ : c₀ ^ q = 1) (hc₀1 : c₀ ≠ 1) :
    IsCyclic G ∨ Nonempty (G ≃* NonabRep c₀ hc₀) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact Nat.mul_ne_zero hp.pos.ne' hq.pos.ne')
  have hcoprime : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  by_cases hcyc : IsCyclic G
  · exact Or.inl hcyc
  refine Or.inr ?_
  obtain ⟨a, b, c, ha, hb, hcq, hc1, hrel⟩ :=
    exists_generators_of_card_eq_prime_mul hp hq hqp hG hcyc
  have hap : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hco : orderOf c = q := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hcq) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hc₀o : orderOf c₀ = q := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hc₀) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc₀1
    · exact h
  -- conjugation by `b^j` raises to power `c^j`.
  have hconj_iter : ∀ j : ℕ, b ^ j * a * (b ^ j)⁻¹ = a ^ (((c ^ j : (ZMod p)ˣ) : ZMod p)).val := by
    intro j
    induction j with
    | zero => simp [ZMod.val_one]
    | succ n ih =>
      have hsplit : b ^ (n + 1) * a * (b ^ (n + 1))⁻¹
          = b * (b ^ n * a * (b ^ n)⁻¹) * b⁻¹ := by rw [pow_succ, mul_inv_rev]; group
      rw [hsplit, ih, ← conj_pow, hrel, ← pow_mul]
      apply pow_eq_pow_iff_modEq.mpr
      rw [ha, show (((c ^ (n + 1) : (ZMod p)ˣ) : ZMod p)).val
            = ((c : ZMod p).val * (((c ^ n : (ZMod p)ˣ) : ZMod p)).val) % p from by
          rw [pow_succ', Units.val_mul, ZMod.val_mul]]
      exact (Nat.mod_modEq _ _).symm
  -- relabel: `c₀ = c^j₀`, so `B = b^j₀` conjugates `a` by `c₀` and has order `q`.
  obtain ⟨j₀, hj₀⟩ := (mem_powers_iff_mem_zpowers (y := c₀)).mpr
    (unit_mem_zpowers_of_pow_eq hp hq.pos c c₀ hco hc₀)
  simp only at hj₀
  have hj₀ne : j₀ ≠ 0 := by
    intro h; rw [h, pow_zero] at hj₀; exact hc₀1 hj₀.symm
  have hgcd : Nat.gcd q j₀ = 1 := by
    have hords : orderOf (c ^ j₀) = q := by rw [hj₀]; exact hc₀o
    rw [orderOf_pow' c hj₀ne, hco] at hords
    exact (Nat.div_eq_self.mp hords).resolve_left hq.pos.ne'
  have hBord : orderOf (b ^ j₀) = q := by rw [orderOf_pow' b hj₀ne, hb, hgcd, Nat.div_one]
  have hBconj : b ^ j₀ * a * (b ^ j₀)⁻¹ = a ^ (c₀ : ZMod p).val := by rw [hconj_iter j₀, hj₀]
  exact nonempty_mulEquiv_nonabRep a (b ^ j₀) ha hBord c₀ hc₀ hBconj hcoprime hG

/-- The classification of groups of order `p * q` (`q ∣ p - 1`), phrased with the two explicit
representatives `ℤ/pq` and `NonabRep c₀`. -/
theorem classification_card_eq_prime_mul' {p q : ℕ} [NeZero p] [NeZero q] (hp : p.Prime)
    (hq : q.Prime) (hqp : q < p) {G : Type*} [Group G] (hG : Nat.card G = p * q)
    (c₀ : (ZMod p)ˣ) (hc₀ : c₀ ^ q = 1) (hc₀1 : c₀ ≠ 1) :
    Nonempty (G ≃* CyclicRep (p * q)) ∨ Nonempty (G ≃* NonabRep c₀ hc₀) := by
  rcases classification_card_eq_prime_mul hp hq hqp hG c₀ hc₀ hc₀1 with hcyc | hnab
  · haveI := hcyc
    exact Or.inl (cyclicRep_classification (Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)) hG)
  · exact Or.inr hnab

/-- `NonabRep c hc` has order `p * q` (restated with the `Nat.card` hypothesis the `Counting`
framework expects). -/
theorem card_nonabRep' [NeZero p] {q : ℕ} [NeZero q] (c : (ZMod p)ˣ) (hc : c ^ q = 1) :
    Nat.card (NonabRep c hc) = p * q := card_nonabRep c hc

end Smallgroups.UsefulTheorems
