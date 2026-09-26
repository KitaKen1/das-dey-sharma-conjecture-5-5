import SemidihedralSubgroups

namespace Conjecture55Semidihedral
noncomputable section

/-- A supplied Klein-four group embeds in any Sylow 2-subgroup. -/
lemma klein_embedding_to_sylow
    {S : Type*} [Group S] [Finite S] (E : Subgroup S)
    (hE : Nat.card E = 4) (Q : Sylow 2 S) :
    ∃ j : E →* Q, Function.Injective j := by
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by simpa using hE)
  obtain ⟨R, hER⟩ := hEp.exists_le_sylow
  exact ⟨(R.equiv Q).toMonoidHom.comp (Subgroup.inclusion hER),
    (R.equiv Q).injective.comp (Subgroup.inclusion_injective hER)⟩

/-- The semidihedral-16 Sylow property passes to a subgroup as either a
smaller dihedral Sylow group or the full semidihedral group. -/
theorem subgroup_sylow_of_semidihedral16
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (eP : P ≃* Conjecture55Semidihedral16.M)
    (S : Subgroup G) (E : Subgroup S)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) (Q : Sylow 2 S) :
    (∃ l, 1 ≤ l ∧ l ≤ 2 ∧ Nonempty (Q ≃* DihedralGroup (2 ^ l))) ∨
      Nonempty (Q ≃* Conjecture55Semidihedral16.M) := by
  obtain ⟨j, hj⟩ := klein_embedding_to_sylow E hE Q
  obtain ⟨i, hi⟩ :=
    Conjecture55SubgroupSylow.exists_injective_hom_to_ambient_sylow 2 P S Q
  exact dihedral_or_semidihedral16_of_embedding
    (eP.toMonoidHom.comp i) (eP.injective.comp hi) j hj hE hsq

theorem subgroup_sylow_of_semidihedral32
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (eP : P ≃* Conjecture55Semidihedral32.M)
    (S : Subgroup G) (E : Subgroup S)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) (Q : Sylow 2 S) :
    (∃ l, 1 ≤ l ∧ l ≤ 3 ∧ Nonempty (Q ≃* DihedralGroup (2 ^ l))) ∨
      Nonempty (Q ≃* Conjecture55Semidihedral32.M) := by
  obtain ⟨j, hj⟩ := klein_embedding_to_sylow E hE Q
  obtain ⟨i, hi⟩ :=
    Conjecture55SubgroupSylow.exists_injective_hom_to_ambient_sylow 2 P S Q
  exact dihedral_or_semidihedral32_of_embedding
    (eP.toMonoidHom.comp i) (eP.injective.comp hi) j hj hE hsq

/-- If the Sylow order decreases on passing to the subgroup, the
semidihedral alternative is impossible and the existing dihedral route applies. -/
theorem subgroup_sylow_dihedral_of_semidihedral32_of_card_lt
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (eP : P ≃* Conjecture55Semidihedral32.M)
    (S : Subgroup G) (E : Subgroup S)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) (Q : Sylow 2 S)
    (hlt : Nat.card Q < Nat.card P) :
    ∃ l, 1 ≤ l ∧ l ≤ 3 ∧ Nonempty (Q ≃* DihedralGroup (2 ^ l)) := by
  rcases subgroup_sylow_of_semidihedral32 P eP S E hE hsq Q with hD | hSD
  · exact hD
  · obtain ⟨eQ⟩ := hSD
    have hc : Nat.card Q = Nat.card P := Nat.card_congr (eQ.trans eP.symm).toEquiv
    omega

theorem subgroup_sylow_dihedral_of_semidihedral16_of_card_lt
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (eP : P ≃* Conjecture55Semidihedral16.M)
    (S : Subgroup G) (E : Subgroup S)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) (Q : Sylow 2 S)
    (hlt : Nat.card Q < Nat.card P) :
    ∃ l, 1 ≤ l ∧ l ≤ 2 ∧ Nonempty (Q ≃* DihedralGroup (2 ^ l)) := by
  rcases subgroup_sylow_of_semidihedral16 P eP S E hE hsq Q with hD | hSD
  · exact hD
  · obtain ⟨eQ⟩ := hSD
    have hc : Nat.card Q = Nat.card P := Nat.card_congr (eQ.trans eP.symm).toEquiv
    omega

#print axioms klein_embedding_to_sylow
#print axioms subgroup_sylow_of_semidihedral16
#print axioms subgroup_sylow_of_semidihedral32
#print axioms subgroup_sylow_dihedral_of_semidihedral16_of_card_lt
#print axioms subgroup_sylow_dihedral_of_semidihedral32_of_card_lt
end
end Conjecture55Semidihedral
