import Modular16Model
import TransferIndexTwo
import Conjecture55Foundation

/-! Excluding the modular Sylow group M16 when its index is squarefree.
The proof constructs an index-two normal subgroup with Sylow group C4 × C2. -/
namespace Conjecture55Modular16
open Conjecture55TransferCharacter Conjecture55Lean4Web

noncomputable def kernelEquivOfEquiv {P : Type*} [Group P] (e : P ≃* M) :
    (parity.comp e.toMonoidHom).ker ≃* A := by
  let k : (parity.comp e.toMonoidHom).ker ≃* parity.ker :=
    { toFun := fun x => ⟨e x.val, x.property⟩
      invFun := fun y => ⟨e.symm y.val, by
        change parity (e (e.symm y.val)) = 1
        rw [e.apply_symm_apply]
        exact y.property⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val)
      map_mul' := fun x y => Subtype.ext (e.map_mul x.val y.val) }
  exact k.trans kernelEquiv

theorem exists_normal_index_two_of_modular_sylow
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (e : P ≃* M) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧
      ∃ Q : Sylow 2 N, Nonempty (Q ≃* A) ∧ Q.index = P.index := by
  let f : P →* C2 := parity.comp e.toMonoidHom
  have hf : Function.Surjective f := parity_surjective.comp e.surjective
  have hker (x : P) : f x = 1 ↔ x ^ 4 = 1 := by
    change parity (e x) = 1 ↔ x ^ 4 = 1
    rw [parity_eq_one_iff, ← map_pow, e.map_eq_one_iff]
  obtain ⟨N, hN, hi, Q, ⟨eQ⟩, hQi⟩ := exists_normal_index_two_of_character P f hf
    (conjugacy_invariant_of_power_kernel (P : Subgroup G) f 4 hker)
  exact ⟨N, hN, hi, Q, ⟨eQ.trans (kernelEquivOfEquiv e)⟩, hQi⟩

/-- This is an unconditional squarefree-index solvability theorem for a
Sylow group actually isomorphic to M16; it uses no FC counting assumption. -/
theorem isSolvable_of_modular16_sylow_of_squarefree_index
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (e : P ≃* M) (hs : Squarefree P.index) : Group.IsSolvable G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN, hi, Q, ⟨eQ⟩, hQi⟩ := exists_normal_index_two_of_modular_sylow P e
  letI : N.Normal := hN
  have hNs : Group.IsSolvable N :=
    Conjecture55C4C2.isSolvable_of_c4c2_sylow_of_squarefree_index Q eQ (hQi.symm ▸ hs)
  have hquot : Nat.card (G ⧸ N) = 2 := by rwa [← Subgroup.index_eq_card]
  letI : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hquot
  have hQs : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨hNs, hQs⟩

#print axioms kernelEquivOfEquiv
#print axioms exists_normal_index_two_of_modular_sylow
#print axioms isSolvable_of_modular16_sylow_of_squarefree_index
end Conjecture55Modular16
