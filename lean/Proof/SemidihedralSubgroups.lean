import KleinSubgroupDichotomy
import Semidihedral16Model
import Semidihedral32Model
import GeneralDihedralSylow

namespace Conjecture55Semidihedral
open Conjecture55GeneralDihedralSylow
noncomputable section

/-- Apply a proved element certificate and a concrete dihedral kernel model
to an injectively embedded group containing an actual Klein-four group. -/
theorem dihedral_or_full_of_certificate
    {M D E B : Type*} [Group M] [Finite M] [Group D] [Finite D]
    [Group E] [Finite E] [Group B] [DecidableEq B]
    (π ρ : M →* B)
    (hroot : Nat.card {x : M // x ^ 2 = 1 ∧ ρ x = 1} = 2)
    (n : ℕ)
    (hgen : ∀ y z : M, π y ≠ 1 → z ^ 2 = 1 → ρ z ≠ 1 →
      ∀ g : M, ∃ i : Fin n, ∃ j : Fin 2,
        g = (if ρ y = 1 then y else y * z) ^ i.val * z ^ j.val)
    {k : ℕ} (hk : 1 ≤ k) (eK : π.ker ≃* DihedralGroup (2 ^ k))
    (i : D →* M) (hi : Function.Injective i)
    (j : E →* D) (hj : Function.Injective j)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    (∃ l, 1 ≤ l ∧ l ≤ k ∧ Nonempty (D ≃* DihedralGroup (2 ^ l))) ∨
      Nonempty (D ≃* M) := by
  let eR : D ≃* i.range := MonoidHom.ofInjective hi
  rcases subgroup_le_ker_or_eq_top π ρ hroot n hgen i.range
      (eR.toMonoidHom.comp j) (eR.injective.comp hj) hE hsq with hle | htop
  · left
    let f : D →* π.ker := (Subgroup.inclusion hle).comp eR.toMonoidHom
    have hf : Function.Injective f := (Subgroup.inclusion_injective hle).comp eR.injective
    have hnc := not_cyclic_of_card_four_exponent_two_embedding hE hsq j hj
    exact dihedral_of_noncyclic_embedding hk hnc
      (eK.toMonoidHom.comp f) (eK.injective.comp hf)
  · right
    exact ⟨MulEquiv.ofBijective i ⟨hi, MonoidHom.range_eq_top.mp htop⟩⟩

theorem dihedral_or_semidihedral16_of_embedding
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    (i : D →* Conjecture55Semidihedral16.M) (hi : Function.Injective i)
    (j : E →* D) (hj : Function.Injective j)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    (∃ l, 1 ≤ l ∧ l ≤ 2 ∧ Nonempty (D ≃* DihedralGroup (2 ^ l))) ∨
      Nonempty (D ≃* Conjecture55Semidihedral16.M) := by
  exact dihedral_or_full_of_certificate Conjecture55Semidihedral16.parity
    Conjecture55Semidihedral16.reflection Conjecture55Semidihedral16.cyclic_involutions_card
    8 Conjecture55Semidihedral16.generation_certificate (by decide : 1 ≤ 2)
    Conjecture55Semidihedral16.evenEquiv i hi j hj hE hsq

theorem dihedral_or_semidihedral32_of_embedding
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    (i : D →* Conjecture55Semidihedral32.M) (hi : Function.Injective i)
    (j : E →* D) (hj : Function.Injective j)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    (∃ l, 1 ≤ l ∧ l ≤ 3 ∧ Nonempty (D ≃* DihedralGroup (2 ^ l))) ∨
      Nonempty (D ≃* Conjecture55Semidihedral32.M) := by
  exact dihedral_or_full_of_certificate Conjecture55Semidihedral32.parity
    Conjecture55Semidihedral32.reflection Conjecture55Semidihedral32.cyclic_involutions_card
    16 Conjecture55Semidihedral32.generation_certificate (by decide : 1 ≤ 3)
    Conjecture55Semidihedral32.evenEquiv i hi j hj hE hsq

#print axioms dihedral_or_full_of_certificate
#print axioms dihedral_or_semidihedral16_of_embedding
#print axioms dihedral_or_semidihedral32_of_embedding
end
end Conjecture55Semidihedral
