import DirectSmallSylow
import CounterexampleModels

/-! Every radical-free strict FC candidate reaches either a dihedral Sylow
model or one of the two full semidihedral models, without Amiri or exact-root. -/
namespace Conjecture55DirectSylow
open Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55VerifiedV4 Conjecture55CounterexampleModels
open Smallgroups.UsefulTheorems Conjecture55OrderThirtyTwo

theorem sylow_alternatives
    {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {a m : ℕ} (hm : Odd m) (P : Sylow 2 G)
    (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    (∃ l, 1 ≤ l ∧ l ≤ 4 ∧ Nonempty (P ≃* DihedralGroup (2 ^ l))) ∨
    (a = 4 ∧ Squarefree m ∧ Nonempty (P ≃* order16_wild_G2)) ∨
    (a = 5 ∧ Squarefree m ∧ Nonempty (P ≃* Semidihedral32)) := by
  obtain ⟨ha, ha5, _⟩ := two_part_and_odd_factorization hrad hm P hcard hlt
  have hacases : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
  rcases hacases with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨1, by decide, by decide,
      Conjecture55DirectSmallSylow.radicalFree_sylow_four_dihedral hrad hm P hcard⟩
  · exact Or.inl ⟨2, by decide, by decide,
      Conjecture55DirectSmallSylow.radicalFree_sylow_eight_dihedral hrad hm P hcard hlt⟩
  · obtain ⟨hsf, hS | hD⟩ := radicalFree_sylow16_two_cases hrad hm P hcard hlt
    · exact Or.inr (Or.inl ⟨rfl, hsf, hS⟩)
    · exact Or.inl ⟨3, by decide, by decide, hD⟩
  · obtain ⟨hsf, hS | hD⟩ := radicalFree_sylow32_two_cases hrad hm P hcard hlt
    · exact Or.inr (Or.inr ⟨rfl, hsf, hS⟩)
    · exact Or.inl ⟨4, by decide, by decide, hD⟩

/-- The actual simple normal subgroup inherits precisely these alternatives.
The full semidihedral alternative also retains the squarefree odd part. -/
theorem simple_normal_alternatives
    {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {a m : ℕ} (hm : Odd m) (P : Sylow 2 G)
    (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ∃ S : Subgroup G, S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ ∧
      ∀ Q : Sylow 2 S,
        (∃ l, 1 ≤ l ∧ l ≤ 4 ∧ Nonempty (Q ≃* DihedralGroup (2 ^ l))) ∨
        (a = 4 ∧ Squarefree m ∧ Nonempty (Q ≃* order16_wild_G2)) ∨
        (a = 5 ∧ Squarefree m ∧ Nonempty (Q ≃* Semidihedral32)) := by
  have hP := sylow_alternatives hrad hm P hcard hlt
  obtain ⟨S, hSn, hSs, hSc, hC⟩ := counterexample_simple_normal hrad hm P hcard hlt
  obtain ⟨E, hE, hsq⟩ := simple_klein_four S hSs hSc
  refine ⟨S, hSn, hSs, hSc, hC, ?_⟩
  intro Q
  rcases hP with ⟨k, hk, hk4, ⟨eP⟩⟩ | ⟨ha, hsf, ⟨eP⟩⟩ | ⟨ha, hsf, ⟨eP⟩⟩
  · obtain ⟨l, hl, hlk, he⟩ :=
      Conjecture55GeneralDihedralSylow.sylow_dihedral_of_contains_card_four_exponent_two
        hk P eP S E hE hsq Q
    exact Or.inl ⟨l, hl, hlk.trans hk4, he⟩
  · rcases Conjecture55Semidihedral.subgroup_sylow_of_semidihedral16 P eP S E hE hsq Q with
      ⟨l, hl, hl2, he⟩ | he
    · exact Or.inl ⟨l, hl, by omega, he⟩
    · exact Or.inr (Or.inl ⟨ha, hsf, he⟩)
  · rcases Conjecture55Semidihedral.subgroup_sylow_of_semidihedral32 P eP S E hE hsq Q with
      ⟨l, hl, hl3, he⟩ | he
    · exact Or.inl ⟨l, hl, by omega, he⟩
    · exact Or.inr (Or.inr ⟨ha, hsf, he⟩)

#print axioms sylow_alternatives
#print axioms simple_normal_alternatives
end Conjecture55DirectSylow
