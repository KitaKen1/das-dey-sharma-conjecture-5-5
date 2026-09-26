import RootDivisibilityInput
import ExponentReduction
import OddRootBypass
import RootAssembly

/-! The actual Frobenius proof discharges the root lower-bound hypotheses.
No Amiri comparison or exact-root theorem is used in the exponent reductions.
The full FC theorem remains conditional on the stated structural inputs. -/
namespace Conjecture55CompletedBounds
open Conjecture55Lean4Web Conjecture55Lean4Web Conjecture55FrobeniusProof
open scoped IsMulCommutative
universe u

theorem cyclic_count_ge_of_sylow_exponent
    {G : Type u} [Group G] [Fintype G] {s a m : ℕ}
    (hs : 1 ≤ s) (hsa : s ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hP : ∀ x : P, x ^ (2 ^ s) = 1)
    (hcard : Nat.card G = 2 ^ a * m) :
    (s - 1 + 2 ^ (a - s + 1)) * m.divisors.card ≤ cyc G :=
  RootWeights.cyclic_count_ge_of_sylow_exponent_bound hs hsa hm P hP hcard
    (rootCountLowerBound G)

theorem cyclic_count_ge_of_noncyclic_sylow
    {G : Type u} [Group G] [Fintype G] {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬IsCyclic P) (hcard : Nat.card G = 2 ^ a * m) :
    (a + 2) * m.divisors.card ≤ cyc G :=
  RootWeights.cyclic_count_ge_of_noncyclic_sylow ha hm P hnc hcard (rootCountLowerBound G)

theorem counterexample_order_shape
    {G : Type u} [Group G] [Fintype G] {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ((a = 2 ∨ a = 3) ∧ (∀ p, m.factorization p ≤ 2) ∧
      ∀ p q, 2 ≤ m.factorization p → 2 ≤ m.factorization q → p = q) ∨
    ((a = 4 ∨ a = 5) ∧ Squarefree m) :=
  Conjecture55ExponentShape.odd_part_shape_of_noncyclic_sylow ha hm P hnc hcard
    (rootCountLowerBound G) hlt

theorem counterexample_cyclic_index_two
    {G : Type u} [Group G] [Fintype G] {a m : ℕ} (ha : 3 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ∃ C : Subgroup P, IsCyclic C ∧ C.index = 2 :=
  RootWeights.exists_cyclic_index_two_of_strict_fc_bound ha hm P hnc hcard
    (rootCountLowerBound G) hlt

theorem counterexample_simple_normal
    {G : Type u} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hV4 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H →
      ∃ E : Subgroup H, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1)
    {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m) (P : Sylow 2 G)
    (hnc : ¬IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ∃ S : Subgroup G, S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ :=
  Conjecture55ExponentReduction.exists_simple_normal_of_strict_fc_bound
    hrad hV4 ha hm P hnc hcard (rootCountLowerBound G) hlt

/-- The previously four-input FC assembly now has three remaining inputs.
The exact-root subgroup input, in particular, is still an explicit hypothesis. -/
theorem affirmative_target_of_three_root_structural_inputs
    (hV4 : Conjecture55Assembly.SimpleKleinFourInput)
    (hclassification : Conjecture55Assembly.SimpleDihedralInput)
    (hexact : Conjecture55Frobenius.ExactRootSubgroupInput.{0}) :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  Conjecture55RootAssembly.affirmative_target_of_four_root_structural_inputs
    hV4 hclassification provedRootDivisibilityInput hexact

#print axioms cyclic_count_ge_of_sylow_exponent
#print axioms cyclic_count_ge_of_noncyclic_sylow
#print axioms counterexample_order_shape
#print axioms counterexample_cyclic_index_two
#print axioms counterexample_simple_normal
#print axioms affirmative_target_of_three_root_structural_inputs
end Conjecture55CompletedBounds
