/-
Copyright (c) 2026 Contributors to the Conjecture 5.5 formalization.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import FeitThompson.FinalTheorem
import BenderSuzuki.PFAppendixII.proposition_1

/-!
Adapters from the actual Qiuzhen odd-order and Brauer–Suzuki endpoints
to universe-polymorphic statements about finite nonabelian simple groups.
-/
namespace Conjecture55V4

/-- A finite nonabelian simple group contains an exponent-two subgroup of order four. -/
theorem exists_order_four_exponent_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G) :
    ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnoOdd : ¬ Odd (Nat.card G) := by
    intro hodd
    apply hnonab
    exact isMulCommutative_iff.mpr
      ((IsSimpleGroup.comm_iff_isSolvable).mpr (odd_order_theorem G hodd))
  have htwo : 2 ∣ Nat.card G := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnoOdd)
  obtain ⟨u, huorder⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 htwo
  have hune : u ≠ 1 := by
    intro h
    simp [h] at huorder
  have hu : BenderSuzuki.PFAppendixIII.IsInvolution u :=
    ⟨hune, by rw [← huorder, pow_orderOf_eq_one]⟩
  have hcore : pPrimeCore 2 G = ⊥ := by
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pPrimeCore 2 G) pPrimeCore_normal).resolve_right
    intro htop
    have hc := pPrimeCore_coprime_card (p := 2) (G := G)
    rw [htop, Subgroup.card_top] at hc
    exact hnoOdd hc.odd_of_left
  have hcenter : Subgroup.center G = ⊥ := by
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center G) inferInstance).resolve_right
    intro htop
    exact hnonab (Subgroup.center_eq_top_iff.mp htop)
  by_contra hmissing
  have hfactor :=
    BenderSuzuki.PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
      (G := G) hmissing hu
  have hcentralizer : Subgroup.centralizer ({u} : Set G) = ⊤ := by
    simpa only [hcore, bot_sup_eq] using hfactor
  have humem : u ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [hcentralizer]
      trivial
    exact (Subgroup.mem_centralizer_iff.mp hg u (by simp)).symm
  exact hune (Subgroup.mem_bot.mp (by simpa only [hcenter] using humem))

/-- The actual universal divisibility input needed by the socle reduction. -/
theorem four_dvd_card_of_nonabelian_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G) : 4 ∣ Nat.card G := by
  obtain ⟨E, hcard, -⟩ := exists_order_four_exponent_two hnonab
  simpa only [hcard] using E.card_subgroup_dvd_card

#print axioms exists_order_four_exponent_two
#print axioms four_dvd_card_of_nonabelian_simple
#print axioms odd_order_theorem
#print axioms BenderSuzuki.PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
end Conjecture55V4
