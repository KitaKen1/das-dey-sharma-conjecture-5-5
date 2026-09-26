import DihedralSubgroupsStandalone
import SmallGroups

/-! Subgroup Sylow groups inherit an arbitrary finite dihedral 2-group
model once an actual Klein-four subgroup excludes the cyclic alternative.
The elementary subgroup classification was independently rechecked, and
the Gorenstein-Walter classification itself is not used. -/

namespace Conjecture55GeneralDihedralSylow
noncomputable section

theorem dihedral_of_noncyclic_embedding
    {D : Type*} [Group D] [Finite D] {k : ℕ} (hk : 1 ≤ k)
    (hnc : ¬ IsCyclic D) (i : D →* DihedralGroup (2 ^ k))
    (hi : Function.Injective i) :
    ∃ l, 1 ≤ l ∧ l ≤ k ∧ Nonempty (D ≃* DihedralGroup (2 ^ l)) := by
  let eR : D ≃* i.range := MonoidHom.ofInjective hi
  rcases Conjecture55DihedralStructure.subgroups_dihedral_twoGroup_cyclic_or_dihedral
      hk i.range with hcyc | ⟨l, hl, ⟨eH⟩⟩
  · let : IsCyclic i.range := hcyc
    exact False.elim (hnc (isCyclic_of_injective eR.toMonoidHom eR.injective))
  · let e : D ≃* DihedralGroup (2 ^ l) := eR.trans eH
    have hcard : Nat.card D = 2 * 2 ^ l :=
      (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    have hd := Subgroup.card_dvd_of_injective i hi
    rw [hcard, DihedralGroup.nat_card] at hd
    have hp : 2 ^ l ∣ 2 ^ k :=
      (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hd
    exact ⟨l, hl, (Nat.pow_dvd_pow_iff_le_right Nat.prime_two.one_lt).mp hp, ⟨e⟩⟩

theorem not_cyclic_of_card_four_exponent_two_embedding
    {E D : Type*} [Group E] [Group D] [Finite E]
    (hE : Nat.card E = 4) (hpow : ∀ x : E, x ^ 2 = 1)
    (j : E →* D) (hj : Function.Injective j) : ¬ IsCyclic D := by
  intro hD
  let : IsCyclic D := hD
  let : IsCyclic E := isCyclic_of_injective j hj
  have hd : Nat.card E ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
  norm_num [hE] at hd

/-- A subgroup containing a Klein-four group has dihedral Sylow 2-subgroups
whenever the ambient group has a dihedral Sylow 2-subgroup, of any order. -/
theorem sylow_dihedral_of_contains_card_four_exponent_two
    {G : Type*} [Group G] [Finite G] {k : ℕ} (hk : 1 ≤ k)
    (P : Sylow 2 G) (eP : P ≃* DihedralGroup (2 ^ k))
    (S : Subgroup G) (E : Subgroup S)
    (hE : Nat.card E = 4) (hpow : ∀ x : E, x ^ 2 = 1)
    (Q : Sylow 2 S) :
    ∃ l, 1 ≤ l ∧ l ≤ k ∧ Nonempty (Q ≃* DihedralGroup (2 ^ l)) := by
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by simpa using hE)
  obtain ⟨R, hER⟩ := hEp.exists_le_sylow
  let j : E →* Q := (R.equiv Q).toMonoidHom.comp (Subgroup.inclusion hER)
  have hj : Function.Injective j :=
    (R.equiv Q).injective.comp (Subgroup.inclusion_injective hER)
  have hnc := not_cyclic_of_card_four_exponent_two_embedding hE hpow j hj
  obtain ⟨i, hi⟩ :=
    Conjecture55SubgroupSylow.exists_injective_hom_to_ambient_sylow 2 P S Q
  exact dihedral_of_noncyclic_embedding hk hnc
    (eP.toMonoidHom.comp i) (eP.injective.comp hi)

end
end Conjecture55GeneralDihedralSylow

#print axioms Conjecture55GeneralDihedralSylow.dihedral_of_noncyclic_embedding
#print axioms Conjecture55GeneralDihedralSylow.not_cyclic_of_card_four_exponent_two_embedding
#print axioms Conjecture55GeneralDihedralSylow.sylow_dihedral_of_contains_card_four_exponent_two
