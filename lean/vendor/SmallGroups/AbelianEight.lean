/-
Copyright (c) 2026 Contributors to the Conjecture 5.5 formalization.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

/-! Elementary classification of abelian groups of order eight. -/

namespace AbelianEight
noncomputable section

variable {G : Type*} [Group G] [Finite G]

theorem orderOf_dvd_four_of_card_eight_not_cyclic
    (hcard : Nat.card G = 8) (hnc : ¬ IsCyclic G) (g : G) : orderOf g ∣ 4 := by
  have hd : orderOf g ∣ 2 ^ 3 := by simpa [hcard] using orderOf_dvd_natCard g
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · simp [he]
  · simp [he]
  · simp [he]
  · exact False.elim (hnc (isCyclic_of_orderOf_eq_card g (by simpa [hcard] using he)))

theorem exists_order_four_of_not_exponent_two
    (hcard : Nat.card G = 8) (hnc : ¬ IsCyclic G)
    (hnot : ¬ ∀ x : G, x ^ 2 = 1) : ∃ x : G, orderOf x = 4 := by
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  have hd : orderOf x ∣ 2 ^ 2 := orderOf_dvd_four_of_card_eight_not_cyclic hcard hnc x
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hnotdvd : ¬ orderOf x ∣ 2 := by simpa only [orderOf_dvd_iff_pow_eq_one] using hx
  refine ⟨x, ?_⟩
  interval_cases k
  · simp [he] at hnotdvd
  · simp [he] at hnotdvd
  · simpa using he

section CommGroup
variable {H : Type*} [CommGroup H] [Finite H]

theorem exists_independent_involution
    (hcard : Nat.card H = 8) (hfour : ∀ g : H, orderOf g ∣ 4)
    (x : H) (hx : orderOf x = 4) :
    ∃ y : H, y ^ 2 = 1 ∧ y ∉ Subgroup.zpowers x := by
  classical
  let X := Subgroup.zpowers x
  have hXcard : Nat.card X = 4 := by simpa [X] using (Nat.card_zpowers x).trans hx
  have hXindex : X.index = 2 := by
    have hi := X.index_mul_card
    rw [hXcard, hcard] at hi
    omega
  have hXtop : X ≠ ⊤ := by
    intro h
    have : Nat.card X = Nat.card H := by rw [h, Subgroup.card_top]
    omega
  obtain ⟨z, _, hz⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hXtop)
  have hzmem : z ^ 2 ∈ Subgroup.zpowers x := X.sq_mem_of_index_two hXindex z
  have hz4 : z ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hfour z)
  have hrep := (isOfFinOrder_of_finite x).mem_zpowers_iff_mem_range_orderOf.mp hzmem
  obtain ⟨k, hk, hpow⟩ := Finset.mem_image.mp hrep
  have hklt : k < 4 := by simpa [hx] using (Finset.mem_range.mp hk)
  have hkdvd : 4 ∣ k * 2 := by
    rw [← hx]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hpow, ← pow_mul]
    exact hz4
  have hkcases : k = 0 ∨ k = 2 := by omega
  rcases hkcases with hk0 | hk2
  · refine ⟨z, ?_, hz⟩
    simpa [hk0] using hpow.symm
  · refine ⟨z * x⁻¹, ?_, ?_⟩
    · rw [mul_pow, inv_pow, ← hpow, hk2]
      simp
    · intro hy
      apply hz
      have := X.mul_mem hy (Subgroup.mem_zpowers x)
      simpa [mul_assoc] using this


theorem nonempty_mulEquiv_c4_prod_c2_of_independent_involution
    (hcard : Nat.card H = 8) (x y : H)
    (hx : orderOf x = 4) (hy2 : y ^ 2 = 1)
    (hyout : y ∉ Subgroup.zpowers x) :
    Nonempty (H ≃* Multiplicative (ZMod 4 × ZMod 2)) := by
  classical
  let X := Subgroup.zpowers x
  let Y := Subgroup.zpowers y
  have hXcard : Nat.card X = 4 := by simpa [X] using (Nat.card_zpowers x).trans hx
  have hyne : y ≠ 1 := by
    intro hy
    apply hyout
    simp [hy]
  have hy : orderOf y = 2 := orderOf_eq_prime hy2 hyne
  have hYcard : Nat.card Y = 2 := by simpa [Y] using (Nat.card_zpowers y).trans hy
  have hYmem (g : H) (hg : g ∈ Y) : g = 1 ∨ g = y := by
    have hrep := (isOfFinOrder_of_finite y).mem_zpowers_iff_mem_range_orderOf.mp hg
    obtain ⟨k, hk, hpow⟩ := Finset.mem_image.mp hrep
    have hklt : k < 2 := by simpa [hy] using (Finset.mem_range.mp hk)
    interval_cases k
    · left
      simpa using hpow.symm
    · right
      simpa using hpow.symm
  have hdisj : Disjoint X Y := by
    apply Subgroup.disjoint_def.mpr
    intro g hgX hgY
    rcases hYmem g hgY with h1 | hyg
    · exact h1
    · exact False.elim (hyout (hyg ▸ hgX))
  have hcomp : X.IsComplement' Y :=
    Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [hXcard, hYcard, hcard]) hdisj
  let eprod : X × Y ≃* H := MulEquiv.ofBijective (X.subtype.coprod Y.subtype) hcomp
  let eX : X ≃* Multiplicative (ZMod 4) :=
    mulEquivOfCyclicCardEq (by simpa using hXcard)
  let eY : Y ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by simpa using hYcard)
  exact ⟨eprod.symm.trans ((eX.prodCongr eY).trans
    (MulEquiv.prodMultiplicative (ZMod 4) (ZMod 2)).symm)⟩

end CommGroup

/-- Every abelian group of order eight is cyclic, has exponent dividing two,
or is isomorphic to C₄ × C₂. -/
theorem cyclic_or_exponent_two_or_mulEquiv_c4_c2
    [IsMulCommutative G] (hcard : Nat.card G = 8) :
    IsCyclic G ∨ (∀ x : G, x ^ 2 = 1) ∨
      Nonempty (G ≃* Multiplicative (ZMod 4 × ZMod 2)) := by
  classical
  by_cases hcyc : IsCyclic G
  · exact Or.inl hcyc
  right
  by_cases hexp : ∀ x : G, x ^ 2 = 1
  · exact Or.inl hexp
  right
  let : CommGroup G := { ‹Group G› with mul_comm := mul_comm' }
  obtain ⟨x, hx⟩ := exists_order_four_of_not_exponent_two hcard hcyc hexp
  obtain ⟨y, hy2, hyout⟩ := exists_independent_involution hcard
    (orderOf_dvd_four_of_card_eight_not_cyclic hcard hcyc) x hx
  exact nonempty_mulEquiv_c4_prod_c2_of_independent_involution hcard x y hx hy2 hyout

#print axioms orderOf_dvd_four_of_card_eight_not_cyclic
#print axioms exists_order_four_of_not_exponent_two
#print axioms exists_independent_involution
#print axioms nonempty_mulEquiv_c4_prod_c2_of_independent_involution
#print axioms cyclic_or_exponent_two_or_mulEquiv_c4_c2
end
end AbelianEight
