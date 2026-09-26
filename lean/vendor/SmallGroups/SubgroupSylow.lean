/-
Copyright (c) 2026 Contributors to the Conjecture 5.5 formalization.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

namespace Conjecture55SubgroupSylow

/-- A Sylow subgroup of a subgroup embeds into any ambient Sylow subgroup. -/
theorem exists_injective_hom_to_ambient_sylow
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (S : Subgroup G) (Q : Sylow p S) :
    ∃ i : Q →* P, Function.Injective i := by
  obtain ⟨R, hR⟩ := Q.exists_comap_subtype_eq
  let j : Q →* R :=
    { toFun := fun x => ⟨((x : S) : G), by
        change (x : S) ∈ (R : Subgroup G).comap S.subtype
        rw [hR]
        exact x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : R => (z : G)) h
  let e : R ≃* P := R.equiv P
  exact ⟨e.toMonoidHom.comp j, e.injective.comp hj⟩

/-- An order-four group in which every element squares to one is the Klein group. -/
theorem nonempty_dihedral_two_equiv_of_card_four
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 4)
    (hexp : ∀ x : E, x ^ 2 = 1) : Nonempty (E ≃* DihedralGroup 2) := by
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour E :=
    { card_four := hE
      exponent_two := (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
        (fun x hx => orderOf_eq_prime (hexp x) hx) }
  exact IsKleinFour.nonempty_mulEquiv

/-- Containment of a Klein four subgroup rules out the cyclic subgroups of a
Sylow group of order four or eight; the remaining Sylow groups inherit the
ambient dihedral isomorphism. No subgroup classification is assumed. -/
theorem sylow_dihedral_of_contains_card_four_exponent_two
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G)
    (hP : Nonempty (P ≃* DihedralGroup 2) ∨ Nonempty (P ≃* DihedralGroup 4))
    (S : Subgroup G) (E : Subgroup S)
    (hE : Nat.card E = 4) (hexp : ∀ x : E, x ^ 2 = 1)
    (Q : Sylow 2 S) :
    Nonempty (Q ≃* DihedralGroup 2) ∨ Nonempty (Q ≃* DihedralGroup 4) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by simpa using hE)
  obtain ⟨R, hER⟩ := hEp.exists_le_sylow
  let j : E →* R := Subgroup.inclusion hER
  have hj : Function.Injective j := Subgroup.inclusion_injective hER
  have hfour : 4 ∣ Nat.card R := by
    simpa only [hE] using Subgroup.card_dvd_of_injective j hj
  obtain ⟨i, hi⟩ := exists_injective_hom_to_ambient_sylow 2 P S R
  have hdiv := Subgroup.card_dvd_of_injective i hi
  have hPcard : Nat.card P = 4 ∨ Nat.card P = 8 := by
    rcases hP with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ((Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card)
    · obtain ⟨e⟩ := he
      exact Or.inr ((Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card)
  have hRle : Nat.card R ≤ 8 := by
    rcases hPcard with hp4 | hp8
    · have := Nat.le_of_dvd (by omega : 0 < Nat.card P) hdiv
      omega
    · exact Nat.le_of_dvd (by omega) (hp8 ▸ hdiv)
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hRcard : Nat.card R = 4 ∨ Nat.card R = 8 := by
    obtain ⟨k, hk⟩ := hfour
    omega
  let eQR : Q ≃* R := Q.equiv R
  rcases hRcard with hr4 | hr8
  · let eER : E ≃* R := MulEquiv.ofBijective j
      ((Nat.bijective_iff_injective_and_card j).mpr ⟨hj, hE.trans hr4.symm⟩)
    obtain ⟨eE⟩ := nonempty_dihedral_two_equiv_of_card_four hE hexp
    exact Or.inl ⟨eQR.trans (eER.symm.trans eE)⟩
  · rcases hP with he | he
    · obtain ⟨eP⟩ := he
      have hp4 : Nat.card P = 4 := (Nat.card_congr eP.toEquiv).trans DihedralGroup.nat_card
      norm_num [hr8, hp4] at hdiv
    · obtain ⟨eP⟩ := he
      have hp8 : Nat.card P = 8 := (Nat.card_congr eP.toEquiv).trans DihedralGroup.nat_card
      let eRP : R ≃* P := MulEquiv.ofBijective i
        ((Nat.bijective_iff_injective_and_card i).mpr ⟨hi, hr8.trans hp8.symm⟩)
      exact Or.inr ⟨eQR.trans (eRP.trans eP)⟩

#print axioms exists_injective_hom_to_ambient_sylow
#print axioms nonempty_dihedral_two_equiv_of_card_four
#print axioms sylow_dihedral_of_contains_card_four_exponent_two

end Conjecture55SubgroupSylow
