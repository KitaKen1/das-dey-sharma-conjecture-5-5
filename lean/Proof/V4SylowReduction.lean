import V4StructuralInput
import SemidihedralSylow

namespace Conjecture55VerifiedV4
open Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55OrderThirtyTwo Smallgroups.UsefulTheorems
universe u

lemma not_solvable_of_nontrivial_radicalFree
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    ¬ Group.IsSolvable G := by
  intro hs
  let : Group.IsSolvable G := hs
  exact top_ne_bot (hrad ⊤ inferInstance inferInstance)

/-- No supplied Klein-four subgroup or nonsolvability hypothesis is needed
in the nontrivial radical-free order-sixteen branch. -/
theorem radicalFree_sylow16_two_cases
    {G : Type u} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (P : Sylow 2 G) (hcard : Nat.card G = 16 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    Squarefree m ∧ (Nonempty (P ≃* order16_wild_G2) ∨
      Nonempty (P ≃* DihedralGroup 8)) := by
  obtain ⟨E, hE, hsq⟩ := klein_four_of_radicalFree hrad
  exact Conjecture55OrderSixteen.nonsolvable_sylow16_two_cases
    hm P hcard hlt (not_solvable_of_nontrivial_radicalFree hrad) E hE hsq

theorem radicalFree_sylow32_two_cases
    {G : Type u} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (P : Sylow 2 G) (hcard : Nat.card G = 32 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    Squarefree m ∧ (Nonempty (P ≃* Semidihedral32) ∨
      Nonempty (P ≃* DihedralGroup 16)) := by
  obtain ⟨E, hE, hsq⟩ := klein_four_of_radicalFree hrad
  exact Conjecture55OrderThirtyTwo.nonsolvable_sylow32_two_cases
    hm P hcard hlt (not_solvable_of_nontrivial_radicalFree hrad) E hE hsq

/-- The actual simple normal subgroup has a dihedral or full SD16 Sylow
model. Existence of that subgroup and both Klein-four subgroups are proved. -/
theorem simple_normal_sylow16_alternatives
    {G : Type u} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (P : Sylow 2 G) (hcard : Nat.card G = 16 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    Squarefree m ∧ ∃ S : Subgroup G,
      S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ ∧
      ∀ Q : Sylow 2 S,
        (∃ l, 1 ≤ l ∧ l ≤ 3 ∧ Nonempty (Q ≃* DihedralGroup (2 ^ l))) ∨
          Nonempty (Q ≃* order16_wild_G2) := by
  obtain ⟨hsf, hP⟩ := radicalFree_sylow16_two_cases hrad hm P hcard hlt
  obtain ⟨S, hSn, hSs, hSc, hcent⟩ := counterexample_simple_normal hrad hm P
    (show Nat.card G = 2 ^ 4 * m by simpa using hcard) hlt
  obtain ⟨E, hE, hsq⟩ := simple_klein_four S hSs hSc
  refine ⟨hsf, S, hSn, hSs, hSc, hcent, ?_⟩
  intro Q
  rcases hP with hSD | hD
  · obtain ⟨eP⟩ := hSD
    rcases Conjecture55Semidihedral.subgroup_sylow_of_semidihedral16 P eP S E hE hsq Q with
      hsmall | hfull
    · obtain ⟨l, hl, hk, he⟩ := hsmall
      exact Or.inl ⟨l, hl, by omega, he⟩
    · exact Or.inr hfull
  · obtain ⟨eP⟩ := hD
    exact Or.inl (Conjecture55GeneralDihedralSylow.sylow_dihedral_of_contains_card_four_exponent_two
      (by decide : 1 ≤ 3) P eP S E hE hsq Q)

theorem simple_normal_sylow32_alternatives
    {G : Type u} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (P : Sylow 2 G) (hcard : Nat.card G = 32 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    Squarefree m ∧ ∃ S : Subgroup G,
      S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ ∧
      ∀ Q : Sylow 2 S,
        (∃ l, 1 ≤ l ∧ l ≤ 4 ∧ Nonempty (Q ≃* DihedralGroup (2 ^ l))) ∨
          Nonempty (Q ≃* Semidihedral32) := by
  obtain ⟨hsf, hP⟩ := radicalFree_sylow32_two_cases hrad hm P hcard hlt
  obtain ⟨S, hSn, hSs, hSc, hcent⟩ := counterexample_simple_normal hrad hm P
    (show Nat.card G = 2 ^ 5 * m by simpa using hcard) hlt
  obtain ⟨E, hE, hsq⟩ := simple_klein_four S hSs hSc
  refine ⟨hsf, S, hSn, hSs, hSc, hcent, ?_⟩
  intro Q
  rcases hP with hSD | hD
  · obtain ⟨eP⟩ := hSD
    rcases Conjecture55Semidihedral.subgroup_sylow_of_semidihedral32 P eP S E hE hsq Q with
      hsmall | hfull
    · obtain ⟨l, hl, hk, he⟩ := hsmall
      exact Or.inl ⟨l, hl, by omega, he⟩
    · exact Or.inr hfull
  · obtain ⟨eP⟩ := hD
    exact Or.inl (Conjecture55GeneralDihedralSylow.sylow_dihedral_of_contains_card_four_exponent_two
      (by decide : 1 ≤ 4) P eP S E hE hsq Q)

#print axioms not_solvable_of_nontrivial_radicalFree
#print axioms radicalFree_sylow16_two_cases
#print axioms radicalFree_sylow32_two_cases
#print axioms simple_normal_sylow16_alternatives
#print axioms simple_normal_sylow32_alternatives
end Conjecture55VerifiedV4
