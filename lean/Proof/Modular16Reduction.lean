import Modular16Case
import Order16Reduction

/-! The modular case is eliminated from the exact FC order-sixteen reduction. -/
namespace Conjecture55OrderSixteen
open Smallgroups.UsefulTheorems Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55SylowReduction

/-- Under the strict FC inequality, a nonsolvable group of order 16m
containing an actual Klein-four subgroup has semidihedral or dihedral Sylow
2-subgroups. The modular case has been excluded by a proved transfer argument. -/
theorem nonsolvable_sylow16_two_cases
    {G : Type*} [Group G] [Fintype G] {m : ℕ} (hm : Odd m)
    (P : Sylow 2 G) (hcard : Nat.card G = 16 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) (hns : ¬ Group.IsSolvable G)
    (E : Subgroup G) (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    Squarefree m ∧ (Nonempty (P ≃* order16_wild_G2) ∨
      Nonempty (P ≃* DihedralGroup 8)) := by
  obtain ⟨hsf, hcases⟩ := nonsolvable_sylow16_three_cases hm P hcard hlt hns E hE hsq
  refine ⟨hsf, ?_⟩
  rcases hcases with hS | hM | hD
  · exact Or.inl hS
  · obtain ⟨eM⟩ := hM
    have hindex : P.index = m := sylow_index_of_two_part P 4 m hm (by simpa using hcard)
    exact (hns (Conjecture55Modular16.isSolvable_of_modular16_sylow_of_squarefree_index
      P eM (hindex.symm ▸ hsf))).elim
  · exact Or.inr hD

#print axioms nonsolvable_sylow16_two_cases
end Conjecture55OrderSixteen
