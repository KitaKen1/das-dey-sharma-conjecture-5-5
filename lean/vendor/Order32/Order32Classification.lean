/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
The quaternion recognition proof is adapted from Order16_Wild.recog_G5
at ac10670581519957a3e3a7c8e1eae0ec44406954, changing the cyclic order from 8 to 16.
The cyclic-index-two classification below is newly developed in this workspace.
-/
import Order32Models

namespace Conjecture55OrderThirtyTwo
open Multiplicative Conjecture55CyclicIndexTwo
variable {G : Type*} [Group G] [Finite G]

lemma recog_quaternion32 (hcard : Nat.card G = 32) (x t : G)
    (hx_order : orderOf x = 16) (ht2 : t ^ 2 = x ^ 8) (hconj : t * x * t⁻¹ = x⁻¹)
    (htx : t ∉ Subgroup.zpowers x) :
    Nonempty (G ≃* QuaternionGroup 8) := by
  have hx_power : x ^ (2 * 8) = 1 := by
    rw [show 2 * 8 = 16 from rfl, ← hx_order]
    exact pow_orderOf_eq_one x
  set ρ := quaternionHom 8 x t hx_power ht2 hconj with hρ
  have hinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro (i | i) h
    · have hval : ρ (QuaternionGroup.a i) = x ^ i.val := rfl
      rw [hval] at h
      have hdvd : (16 : ℕ) ∣ i.val := by
        have h0 : orderOf x ∣ i.val := orderOf_dvd_of_pow_eq_one h
        rwa [hx_order] at h0
      have hlt : i.val < 16 := ZMod.val_lt i
      have h0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      rw [QuaternionGroup.one_def]
      congr 1
      exact (ZMod.val_eq_zero i).mp h0
    · exfalso
      have hval : ρ (QuaternionGroup.xa i) = t * x ^ i.val := rfl
      rw [hval] at h
      have ht_eq : t = (x ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
      exact htx (ht_eq ▸ Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
  have hcards : Nat.card (QuaternionGroup 8) = Nat.card G := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card, hcard]
  exact ⟨(mulEquivOfInjectiveCard ρ hinj hcards).symm⟩

/-- A noncyclic group of order 32 has exponent dividing 16. -/
lemma pow_sixteen_eq_one (hcard : Nat.card G = 32) (hnc : ¬ IsCyclic G) (x : G) :
    x ^ 16 = 1 := by
  have hd : orderOf x ∣ 2 ^ 5 := by simpa [hcard] using orderOf_dvd_natCard x
  obtain ⟨r, hr, hx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hr4 : r ≤ 4 := by
    by_contra h
    have he : r = 5 := by omega
    exact hnc (isCyclic_of_orderOf_eq_card x (by simpa [he, hcard] using hx))
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hx]
  exact pow_dvd_pow 2 hr4

/-- Complete classification in the only order-32 branch forced by the FC
exponent bound: noncyclic groups with an element of order sixteen. -/
theorem classification_of_order16 (hcard : Nat.card G = 32) (hnc : ¬ IsCyclic G)
    (x : G) (hx : orderOf x = 16) :
    Nonempty (G ≃* Abelian32) ∨ Nonempty (G ≃* Semidihedral32) ∨
    Nonempty (G ≃* Modular32) ∨ Nonempty (G ≃* Dihedral32) ∨
    Nonempty (G ≃* QuaternionGroup 8) := by
  classical
  have hx' : x ^ 16 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hHcard : Nat.card (Subgroup.zpowers x) = 16 := by rw [Nat.card_zpowers, hx]
  have hHidx : (Subgroup.zpowers x).index = 2 := by
    have hmul := (Subgroup.zpowers x).card_mul_index
    rw [hHcard, hcard] at hmul
    omega
  have hHnorm : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hHidx
  obtain ⟨t, ht⟩ : ∃ t : G, t ∉ Subgroup.zpowers x := by
    by_contra hc
    push Not at hc
    have htop : Subgroup.zpowers x = ⊤ := (Subgroup.eq_top_iff' _).mpr hc
    rw [htop, Subgroup.card_top, hcard] at hHcard
    omega
  obtain ⟨m, hm_lt, hm⟩ := exists_pow_eq_of_mem_zpowers (by rw [hx]; norm_num)
    (hHnorm.conj_mem x (Subgroup.mem_zpowers x) t)
  rw [hx] at hm_lt
  have hconjpow : ∀ j : ℕ, t * x ^ j * t⁻¹ = x ^ (m * j) := by
    intro j
    calc t * x ^ j * t⁻¹ = (t * x * t⁻¹) ^ j := by rw [← conj_pow]
      _ = (x ^ m) ^ j := by rw [← hm]
      _ = x ^ (m * j) := by rw [← pow_mul]
  have ht2H : t ^ 2 ∈ Subgroup.zpowers x :=
    (Subgroup.zpowers x).sq_mem_of_index_two hHidx t
  obtain ⟨k, hk_lt, hk⟩ := exists_pow_eq_of_mem_zpowers (by rw [hx]; norm_num) ht2H
  rw [hx] at hk_lt
  have hkeven : k % 2 = 0 := by
    have hd : 16 ∣ k * 8 := by
      rw [← hx]
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, hk, ← pow_mul]
      exact pow_sixteen_eq_one hcard hnc t
    omega
  have hmm : x ^ (m * m) = x ^ 1 := by
    calc x ^ (m * m) = t * x ^ m * t⁻¹ := (hconjpow m).symm
      _ = t * (t * x * t⁻¹) * t⁻¹ := by rw [hm]
      _ = t ^ 2 * x * (t ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = x ^ k * x * (x ^ k)⁻¹ := by rw [← hk]
      _ = x ^ 1 := by group
  have hmod := pow_eq_pow_iff_modEq.mp hmm
  rw [hx] at hmod
  have hm_cases : m = 1 ∨ m = 7 ∨ m = 9 ∨ m = 15 := by
    interval_cases m <;> norm_num [Nat.ModEq] at hmod
    all_goals decide
  have hfix : x ^ (m * k) = x ^ k := by
    calc x ^ (m * k) = t * x ^ k * t⁻¹ := (hconjpow k).symm
      _ = t * t ^ 2 * t⁻¹ := by rw [hk]
      _ = t ^ 2 := by group
      _ = x ^ k := hk.symm
  have hdvd : ∀ c : ℕ, m * k = k + c → 16 ∣ c := by
    intro c hc
    rw [← hx]
    apply orderOf_dvd_of_pow_eq_one
    apply mul_left_cancel (a := x ^ k)
    rw [mul_one, ← pow_add, ← hc]
    exact hfix
  have htwist (j : ℕ) : (x ^ j * t) ^ 2 = x ^ ((m + 1) * j + k) := by
    calc (x ^ j * t) ^ 2 = x ^ j * (t * x ^ j * t⁻¹) * t ^ 2 := by simp only [pow_two]; group
      _ = x ^ j * x ^ (m * j) * x ^ k := by rw [hconjpow, ← hk]
      _ = x ^ ((m + 1) * j + k) := by rw [← pow_add, ← pow_add]; congr 1; ring
  have hout (j : ℕ) : x ^ j * t ∉ Subgroup.zpowers x := by
    intro h
    apply ht
    have hh := (Subgroup.zpowers x).mul_mem
      ((Subgroup.zpowers x).inv_mem ((Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) j)) h
    simpa only [inv_mul_cancel_left] using hh
  have htwistconj (j : ℕ) : (x ^ j * t) * x * (x ^ j * t)⁻¹ = x ^ m := by
    calc (x ^ j * t) * x * (x ^ j * t)⁻¹ = x ^ j * (t * x * t⁻¹) * (x ^ j)⁻¹ := by group
      _ = x ^ j * x ^ m * (x ^ j)⁻¹ := by rw [← hm]
      _ = x ^ m := by group
  rcases hm_cases with rfl | rfl | rfl | rfl
  · left
    have ht' : (x ^ (16 - k / 2) * t) ^ 2 = 1 := by
      rw [htwist, show (1 + 1) * (16 - k / 2) + k = 32 by omega]
      change x ^ (16 * 2) = 1
      rw [pow_mul, hx', one_pow]
    exact recog_c16_split hcard action1 (k := 1) (by decide +kernel) x _ hx ht'
      (hout _) (htwistconj _)
  · right; left
    have hk08 : k = 0 ∨ k = 8 := by have hh := hdvd (6 * k) (by ring); omega
    rcases hk08 with rfl | rfl
    · exact recog_c16_split hcard action7 (k := 7) (by decide +kernel) x t hx
        (by rw [← hk, pow_zero]) ht (by rw [← hm])
    · exact recog_c16_split hcard action7 (k := 7) (by decide +kernel) x (x ^ 1 * t) hx
        (by simpa only [htwist] using hx') (hout _) (htwistconj _)
  · right; right; left
    have ht' : (x ^ (3 * (k / 2)) * t) ^ 2 = 1 := by
      rw [htwist, show (9 + 1) * (3 * (k / 2)) + k = 16 * k by omega,
        pow_mul, hx', one_pow]
    exact recog_c16_split hcard action9 (k := 9) (by decide +kernel) x _ hx ht'
      (hout _) (htwistconj _)
  · have hk08 : k = 0 ∨ k = 8 := by have hh := hdvd (14 * k) (by ring); omega
    rcases hk08 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl (recog_c16_split hcard action15 (k := 15)
        (by decide +kernel) x t hx (by rw [← hk, pow_zero]) ht (by rw [← hm])))))
    · have hxinv : x ^ 15 = x⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ]
        exact hx'
      exact Or.inr (Or.inr (Or.inr (Or.inr (recog_quaternion32 hcard x t hx hk.symm
        (by rw [← hm, hxinv]) ht))))

#print axioms recog_quaternion32
#print axioms pow_sixteen_eq_one
#print axioms classification_of_order16
end Conjecture55OrderThirtyTwo
