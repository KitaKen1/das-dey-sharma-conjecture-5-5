/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Source: lixiang90/smallgroups @ ac10670581519957a3e3a7c8e1eae0ec44406954
Selected generic recognition helpers from Order16_Wild.lean.
Imports, namespace and visibility adapted; proof bodies retained.
-/
import Mathlib

namespace Conjecture55CyclicIndexTwo
open Multiplicative
variable {G : Type*} [Group G]

lemma c2_two_cases (a : Multiplicative (ZMod 2)) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

@[simp] private lemma c2_mul_self : (Multiplicative.ofAdd (1 : ZMod 2)
* Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 := by
  decide

set_option linter.flexible false in

lemma zpow_eq_pow_emod {G : Type*} [Group G] (g : G) {n : ℕ} (hn : 0 < n)
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

lemma exists_pow_eq_of_mem_zpowers {G : Type*} [Group G] {x y : G}
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

noncomputable def zmodPowHom {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift n
    ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_natCast, hg, ofMul_one]⟩

lemma zmodPowHom_apply {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1)
    (k : ℕ) : zmodPowHom n g hg (Multiplicative.ofAdd ((k : ZMod n))) = g ^ k := by
  have h1 : (((k : ℤ)) : ZMod n) = ((k : ZMod n)) := by push_cast; rfl
  simp only [zmodPowHom, AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd]
  rw [← h1, ZMod.lift_coe]
  rw [zmultiplesHom_apply, ← ofMul_zpow, toMul_ofMul, zpow_natCast]

noncomputable def mulEquivOfInjectiveCard {M : Type*} [Group M] [Finite M] [Finite G]
    (Φ : M →* G) (hi : Function.Injective Φ) (hcard : Nat.card M = Nat.card G) : M ≃* G := by
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype G := Fintype.ofFinite G
  exact MulEquiv.ofBijective Φ ((Fintype.bijective_iff_injective_and_card Φ).mpr
    ⟨hi, by rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]⟩)

lemma zmodPowHom_eval {n : ℕ} [NeZero n] (g : G) (hg : g ^ n = 1)
    (m : Multiplicative (ZMod n)) :
    zmodPowHom n g hg m = g ^ (Multiplicative.toAdd m).val := by
  have hm : m = Multiplicative.ofAdd (((Multiplicative.toAdd m).val : ZMod n)) := by
    rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
  conv_lhs => rw [hm]
  exact zmodPowHom_apply n g hg _

lemma zmodPowHom_gen {n : ℕ} (hn : 2 ≤ n) (g : G) (hg : g ^ n = 1) :
    zmodPowHom n g hg (Multiplicative.ofAdd (1 : ZMod n)) = g := by
  haveI : NeZero n := ⟨by omega⟩
  rw [zmodPowHom_eval, toAdd_ofAdd, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn, pow_one]

lemma zmodPowHom_injective {n : ℕ} (hn : 0 < n) (g : G) (hg : g ^ n = 1)
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

lemma recog_split_c2 {N : Type*} [Group N] [Finite N] [Finite G]
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

lemma pow_mod_of_pow_eq_one {g : G} {m : ℕ} (hg : g ^ m = 1) (k : ℕ) :
    g ^ (k % m) = g ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k m]
  rw [pow_add, pow_mul, hg, one_pow, one_mul]

lemma pow_val_add' {g : G} {m : ℕ} [NeZero m] (hg : g ^ m = 1) (i j : ZMod m) :
    g ^ (i + j).val = g ^ i.val * g ^ j.val := by
  rw [ZMod.val_add, pow_mod_of_pow_eq_one hg, pow_add]

def quaternionHom (n : ℕ) [NeZero n] (g t : G)
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

lemma decomp_index_two [Finite G] {H : Subgroup G} [H.Normal] (hidx : H.index = 2)
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

#print axioms c2_two_cases
#print axioms zpow_eq_pow_emod
#print axioms exists_pow_eq_of_mem_zpowers
#print axioms zmodPowHom
#print axioms zmodPowHom_apply
#print axioms mulEquivOfInjectiveCard
#print axioms zmodPowHom_eval
#print axioms zmodPowHom_gen
#print axioms zmodPowHom_injective
#print axioms recog_split_c2
#print axioms pow_mod_of_pow_eq_one
#print axioms pow_val_add'
#print axioms quaternionHom
#print axioms decomp_index_two
end Conjecture55CyclicIndexTwo
