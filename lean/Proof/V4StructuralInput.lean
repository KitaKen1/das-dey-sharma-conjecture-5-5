import V4Simple
import CompletedBounds
import Modular16Reduction
import Order32Reduction

/-! Supply the actual Klein-four theorem to the existing FC reductions.
The final FC assertion remains open; classification inputs below stay explicit. -/
namespace Conjecture55VerifiedV4
open Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55Assembly Conjecture55SylowReduction
universe u

/-- The former simple-group Klein-four input is now a proved theorem. -/
theorem simpleKleinFourInput : SimpleKleinFourInput := by
  intro S _ _ hs hn
  let : IsSimpleGroup S := hs
  exact Conjecture55V4.exists_order_four_exponent_two hn

/-- A universe-polymorphic form for the structural reductions. -/
theorem simple_klein_four (S : Type u) [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hn : ¬ IsMulCommutative S) :
    ∃ E : Subgroup S, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1 := by
  let : IsSimpleGroup S := hs
  exact Conjecture55V4.exists_order_four_exponent_two hn

theorem klein_four_of_radicalFree
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1 :=
  Conjecture55RadicalV4.exists_card_four_exponent_two_of_radicalFree hrad simple_klein_four

/-- The exact FC inequality forces a simple normal subgroup with trivial
centralizer in the radical-free case, without a supplied V4 or Frobenius input. -/
theorem counterexample_simple_normal
    {G : Type u} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {a m : ℕ} (hm : Odd m) (P : Sylow 2 G)
    (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ∃ S : Subgroup G, S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ := by
  obtain ⟨E, hE, hsq⟩ := klein_four_of_radicalFree hrad
  have ha : 2 ≤ a := two_le_exponent_of_four_dvd a m hm (by
    have hd := E.card_subgroup_dvd_card
    rwa [hE, hcard] at hd)
  obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
  have hnc := not_isCyclic_of_card_four_exponent_two_embedding hE hsq f hf
  exact Conjecture55CompletedBounds.counterexample_simple_normal
    hrad simple_klein_four ha hm P hnc hcard hlt

/-- The root-count assembly now has precisely two unproved inputs:
the small-dihedral classification and the exact-root subgroup theorem. -/
theorem affirmative_target_of_two_root_structural_inputs
    (hclassification : SimpleDihedralInput)
    (hexact : Conjecture55Frobenius.ExactRootSubgroupInput.{0}) :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  Conjecture55CompletedBounds.affirmative_target_of_three_root_structural_inputs
    simpleKleinFourInput hclassification hexact

/-- The comparison assembly also no longer needs a Klein-four assumption. -/
theorem affirmative_target_of_comparison_and_classification
    (hcomparison : ComparisonInput) (hclassification : SimpleDihedralInput) :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  Conjecture55Assembly.affirmative_target_of_three_structural_inputs
    simpleKleinFourInput hcomparison hclassification

#print axioms simpleKleinFourInput
#print axioms simple_klein_four
#print axioms klein_four_of_radicalFree
#print axioms counterexample_simple_normal
#print axioms affirmative_target_of_two_root_structural_inputs
#print axioms affirmative_target_of_comparison_and_classification
end Conjecture55VerifiedV4
