/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Order16Library.UsefulTheorems.SchurZassenhaus
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Groups of order `p² q` with `p ∤ q − 1`: the Sylow-`p` subgroup is normal

Let `p`, `q` be distinct primes and `|G| = p² q`. The number of Sylow `p`-subgroups `n_p` divides
`q` and is `≡ 1 [MOD p]`, so `n_p ∈ {1, q}`; and `n_p = q` would force `p ∣ q − 1`. Hence under
`p ∤ q − 1` the Sylow `p`-subgroup is **unique and normal**.

(Note `p ∤ q − 1` already forces `p` odd: if `p = 2` then `q` is an odd prime, so `q − 1` is
even and `2 ∣ q − 1`. So the stated `p ≥ 3` is automatic.)

The normal Sylow `p`-subgroup `P` has order `p²` (so it is abelian, via
`IsPGroup.isMulCommutative_of_card_eq_prime_sq`) and coprime index `q`, so Schur–Zassenhaus
(`schurZassenhaus_semidirectProduct`) splits `G` as a semidirect product:

* `card_sylow_p_eq_one_of_card_psq` — `n_p = 1`;
* `sylow_p_normal_of_card_psq` — the Sylow `p`-subgroup is normal;
* `card_sylow_p_subgroup_of_card_psq` — it has order `p²`;
* `psq_semidirectProduct` — `G ≃* P ⋊[φ] K` with `P` normal of order `p²` and `K` of order `q`.

This reduces the classification to the action `φ : K → Aut P` (handled by
`SemidirectProductClassify.lean`); the further count depends on `q ∣ p − 1` and `q ∣ p + 1` and the
structure of `P`, so it is left to the per-order files.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-- For distinct primes `p, q` with `p ∤ q − 1`, a group of order `p² q` has a **unique** Sylow
`p`-subgroup. -/
theorem card_sylow_p_eq_one_of_card_psq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : ¬ p ∣ q - 1) [Finite G] (hG : Nat.card G = p ^ 2 * q) :
    Nat.card (Sylow p G) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  have hdvdpq : Nat.card (Sylow p G) ∣ p ^ 2 * q :=
    hG ▸ (P0.card_dvd_index.trans (Subgroup.index_dvd_card _))
  have hndvd_p : ¬ p ∣ Nat.card (Sylow p G) := not_dvd_card_sylow p G
  have hcop : Nat.Coprime (Nat.card (Sylow p G)) (p ^ 2) :=
    ((hp.coprime_iff_not_dvd.mpr hndvd_p).symm).pow_right 2
  have hdq : Nat.card (Sylow p G) ∣ q := hcop.dvd_of_dvd_mul_left hdvdpq
  rcases (Nat.dvd_prime hq).mp hdq with h | h
  · exact h
  · exfalso
    have hmod := card_sylow_modEq_one p G
    rw [h] at hmod
    exact hdvd ((Nat.modEq_iff_dvd' (by have := hq.two_le; omega)).mp hmod.symm)

/-- **The Sylow `p`-subgroup of a group of order `p² q` is normal** when `p ∤ q − 1`. -/
theorem sylow_p_normal_of_card_psq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : ¬ p ∣ q - 1) [Finite G] (hG : Nat.card G = p ^ 2 * q) (P : Sylow p G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_p_eq_one_of_card_psq hp hq hdvd hG)).1
  exact normal_of_subsingleton P

/-- The Sylow `p`-subgroup of a group of order `p² q` (with `p ≠ q`) has order `p²`. -/
theorem card_sylow_p_subgroup_of_card_psq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpne : p ≠ q)
    [Finite G] (hG : Nat.card G = p ^ 2 * q) (P : Sylow p G) :
    Nat.card (↑P : Subgroup G) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpndvdq : ¬ p ∣ q := fun h => hpne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hfact : (p ^ 2 * q).factorization p = 2 := by
    rw [Nat.factorization_mul (pow_ne_zero 2 hp.pos.ne') hq.pos.ne', Finsupp.add_apply,
      Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd hpndvdq, add_zero]
  rw [Sylow.card_eq_multiplicity, hG, hfact]

/-- **Schur–Zassenhaus reduction for order `p² q` with `p ∤ q − 1`.** The group splits as a
semidirect product `P ⋊[φ] K` where `P` is the normal Sylow `p`-subgroup (order `p²`, hence abelian)
and `K` is a Sylow `q`-subgroup (order `q`). Classifying such groups now reduces to the action `φ`
(see `SemidirectProductClassify.lean`). -/
theorem psq_semidirectProduct {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpne : p ≠ q)
    (hdvd : ¬ p ∣ q - 1) [Finite G] (hG : Nat.card G = p ^ 2 * q) :
    ∃ (P K : Subgroup G) (φ : K →* MulAut P),
      P.Normal ∧ Nat.card P = p ^ 2 ∧ Nat.card K = q ∧
        Nonempty (G ≃* SemidirectProduct P K φ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_p_normal_of_card_psq hp hq hdvd hG P0
  have hcardP : Nat.card (↑P0 : Subgroup G) = p ^ 2 :=
    card_sylow_p_subgroup_of_card_psq hp hq hpne hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardP]
    exact Nat.Coprime.pow_left 2 (hp.coprime_iff_not_dvd.mpr P0.not_dvd_index)
  obtain ⟨K, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardK : Nat.card K = q := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardP] at h1
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h1).symm
  exact ⟨↑P0, K, φ, hnorm, hcardP, hcardK, ⟨e⟩⟩

end Smallgroups.UsefulTheorems
