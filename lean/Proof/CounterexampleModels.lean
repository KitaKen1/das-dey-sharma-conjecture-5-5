import V4StructuralInput
import PSL2DegreeAtMostTwo
import A7Case

/-! Connect the odd-part bounds of every radical-free FC counterexample
to the actual PSL2/A7 counting endpoints. No classification is assumed here. -/
namespace Conjecture55CounterexampleModels
open Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55Assembly Conjecture55SylowReduction Conjecture55VerifiedV4

theorem two_part_and_odd_factorization
    {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {a m : ℕ} (hm : Odd m) (P : Sylow 2 G)
    (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    2 ≤ a ∧ a ≤ 5 ∧ ∀ p, m.factorization p ≤ 2 := by
  obtain ⟨E, hE, hsq⟩ := klein_four_of_radicalFree hrad
  have ha : 2 ≤ a := two_le_exponent_of_four_dvd a m hm (by
    have hd := E.card_subgroup_dvd_card
    rwa [hE, hcard] at hd)
  obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
  have hnc := not_isCyclic_of_card_four_exponent_two_embedding hE hsq f hf
  rcases Conjecture55CompletedBounds.counterexample_order_shape
    ha hm P hnc hcard hlt with ⟨ha23, hfac, _⟩ | ⟨ha45, hsf⟩
  · exact ⟨ha, by omega, hfac⟩
  · exact ⟨ha, by omega, fun p => (hsf.natFactorization_le_one p).trans (by decide)⟩

/-- In the two-part sizes at least `16`, the strict FC inequality forces the
odd part of the group order to be squarefree. -/
theorem squarefree_of_four_le_two_part
    {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {a m : ℕ} (ha4 : 4 ≤ a) (hm : Odd m) (P : Sylow 2 G)
    (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) : Squarefree m := by
  obtain ⟨E, hE, hsq⟩ := klein_four_of_radicalFree hrad
  have ha : 2 ≤ a := two_le_exponent_of_four_dvd a m hm (by
    have hd := E.card_subgroup_dvd_card
    rwa [hE, hcard] at hd)
  obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
  have hnc := not_isCyclic_of_card_four_exponent_two_embedding hE hsq f hf
  rcases Conjecture55CompletedBounds.counterexample_order_shape
      ha hm P hnc hcard hlt with hsmall | hlarge
  · rcases hsmall.1 with rfl | rfl <;> omega
  · exact hlarge.2

/-- Once an actual normal PSL2 or A7 model with trivial centralizer has
been obtained, the direct exponent route yields a contradiction in all four
remaining two-part sizes. No supplied exponent bound or field degree remains. -/
theorem not_actual_normal_model
    {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {a m : ℕ} (hm : Odd m) (P : Sylow 2 G)
    (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2))
    (S : Subgroup G) [S.Normal]
    (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    ¬ (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ f ∧
        Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f))) := by
  intro hmodel
  have hfac := (two_part_and_odd_factorization hrad hm P hcard hlt).2.2
  apply Nat.not_le_of_gt hlt
  rcases hmodel with hA | ⟨p, f, hp, hpodd, hpq, ⟨eP⟩⟩
  · obtain ⟨eA⟩ := hA
    exact Conjecture55A7Count.threshold_le_of_normal_a7_trivial_centralizer S eA.symm hC
  · let : Fact p.Prime := hp
    have hf : 1 ≤ f := by
      by_contra h
      have hf0 : f = 0 := by omega
      simp [hf0] at hpq
    exact Conjecture55DegreeAtMostTwo.threshold_le_of_normal_galoisField_psl2_factorization_le_two
      p f a m hpodd hf hpq hm hcard hfac S eP.symm hC

#print axioms two_part_and_odd_factorization
#print axioms squarefree_of_four_le_two_part
#print axioms not_actual_normal_model
end Conjecture55CounterexampleModels
