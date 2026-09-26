import Order32Classification
import Quaternion32Roots
import C16C2Case
import Modular32Case
import CompletedBounds

/-! The order-32 branch for the exact Formal Conjectures counting functions.
An actual Klein-four subgroup is still an explicit input. -/
namespace Conjecture55OrderThirtyTwo
open Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55FrobeniusProof Conjecture55SylowReduction

/-- The strict FC bound gives exactly five candidates in the noncyclic
order-32 Sylow branch; this is not a classification of all groups of order 32. -/
theorem counterexample_sylow32_candidates
    {G : Type*} [Group G] [Fintype G] {m : ℕ} (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P)
    (hcard : Nat.card G = 32 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    Nonempty (P ≃* Abelian32) ∨ Nonempty (P ≃* Semidihedral32) ∨
    Nonempty (P ≃* Modular32) ∨ Nonempty (P ≃* Dihedral32) ∨
    Nonempty (P ≃* QuaternionGroup 8) := by
  have hc : Nat.card G = 2 ^ 5 * m := by simpa using hcard
  have hP : Nat.card P = 32 := by
    simpa using RootWeights.sylow_card_eq_two_part P hm hc
  obtain ⟨x, hx⟩ := RootWeights.exists_order_half_sylow_card_of_strict_fc_bound
    (by decide : 3 ≤ 5) hm P hnc hc (rootCountLowerBound G) hlt
  exact classification_of_order16 hP hnc x (by simpa using hx)

/-- For a nonsolvable strict-FC candidate with an actual Klein-four subgroup,
only SD32 and Mathlib's D32 remain. The abelian, modular and quaternion types
are excluded by proved solvability and embedding arguments. -/
theorem nonsolvable_sylow32_two_cases
    {G : Type*} [Group G] [Fintype G] {m : ℕ} (hm : Odd m)
    (P : Sylow 2 G) (hcard : Nat.card G = 32 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) (hns : ¬ Group.IsSolvable G)
    (E : Subgroup G) (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    Squarefree m ∧ (Nonempty (P ≃* Semidihedral32) ∨
      Nonempty (P ≃* DihedralGroup 16)) := by
  obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
  have hnc := not_isCyclic_of_card_four_exponent_two_embedding hE hsq f hf
  have hc : Nat.card G = 2 ^ 5 * m := by simpa using hcard
  have hsf : Squarefree m := by
    have hshape := Conjecture55CompletedBounds.counterexample_order_shape
      (by decide : 2 ≤ 5) hm P hnc hc hlt
    rcases hshape with ⟨ha, _, _⟩ | ⟨_, hsf⟩
    · norm_num at ha
    · exact hsf
  have hindex : P.index = m := sylow_index_of_two_part P 5 m hm hc
  refine ⟨hsf, ?_⟩
  rcases counterexample_sylow32_candidates hm P hnc hcard hlt with
    hA | hS | hM | hD | hQ
  · obtain ⟨eA⟩ := hA
    exact (hns (Conjecture55C16C2.isSolvable_of_c16c2_sylow_of_squarefree_index
      P (eA.trans abelian32Equiv) (hindex.symm ▸ hsf))).elim
  · exact Or.inl hS
  · obtain ⟨eM⟩ := hM
    exact (hns (Conjecture55Modular32.isSolvable_of_modular32_sylow_of_squarefree_index
      P eM (hindex.symm ▸ hsf))).elim
  · obtain ⟨eD⟩ := hD
    exact Or.inr ⟨eD.trans dihedral32Equiv⟩
  · obtain ⟨eQ⟩ := hQ
    have hle := card_le_two_of_embedding_quaternion32
      (eQ.toMonoidHom.comp f) (eQ.injective.comp hf) hsq
    omega

#print axioms counterexample_sylow32_candidates
#print axioms nonsolvable_sylow32_two_cases
end Conjecture55OrderThirtyTwo
