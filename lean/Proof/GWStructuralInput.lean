import GWAdapterCore
import GorensteinWalter.FinalTheorem
import V4StructuralInput

/-! Actual GW endpoints. This file is accepted only after the complete
upstream proof and these declarations pass the standard-axiom audit. -/
namespace Conjecture55GWAdapter
universe u

theorem simpleDihedralInput : Conjecture55Assembly.SimpleDihedralInput :=
  simpleDihedralInput_of_gorensteinWalterStatement GorensteinWalter.gorensteinWalter

theorem simple_model_of_dihedral_sylow
    (G : Type u) [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ¬IsMulCommutative G)
    {l : ℕ} (hl : 1 ≤ l) (P : Sylow 2 G)
    (e : P ≃* DihedralGroup (2 ^ l)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ f ∧
        Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) :=
  simple_model_of_dihedral_sylow_of_statement GorensteinWalter.gorensteinWalter
    G hs hn hl P e

/-- The exact-root route now retains only the explicit exact-root subgroup input. -/
theorem affirmative_target_of_exact_root_subgroup
    (hexact : Conjecture55Frobenius.ExactRootSubgroupInput.{0}) :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      Conjecture55Lean4Web.cyc G < 2 ^ (Conjecture55Lean4Web.numPrimeFactors G + 2) →
        Group.IsSolvable G :=
  Conjecture55VerifiedV4.affirmative_target_of_two_root_structural_inputs
    simpleDihedralInput hexact

#print axioms simpleDihedralInput
#print axioms simple_model_of_dihedral_sylow
#print axioms affirmative_target_of_exact_root_subgroup
end Conjecture55GWAdapter
