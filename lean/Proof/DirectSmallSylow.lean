import OddComplementSolvability
import V4SylowReduction

/-! The small Sylow branches of the direct exponent route use neither
Amiri's comparison nor the exact-root subgroup theorem. -/
namespace Conjecture55DirectSmallSylow
open Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55SylowReduction Conjecture55VerifiedV4

theorem radicalFree_sylow_eight_dihedral
    {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (P : Sylow 2 G) (hcard : Nat.card G = 8 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    Nonempty (P ≃* DihedralGroup 4) := by
  obtain ⟨E, hE, hsq⟩ := klein_four_of_radicalFree hrad
  obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
  have hnc := not_isCyclic_of_card_four_exponent_two_embedding hE hsq f hf
  have hc : Nat.card G = 2 ^ 3 * m := by simpa using hcard
  have hP : Nat.card P = 8 := by
    simpa using sylow_card_of_two_part P 3 m hm hc
  obtain ⟨x, hx⟩ := RootWeights.exists_order_half_sylow_card_of_strict_fc_bound
    (by decide : 3 ≤ 3) hm P hnc hc
    (Conjecture55FrobeniusProof.rootCountLowerBound G) hlt
  have hx4 : orderOf x = 4 := by simpa using hx
  rcases Conjecture55OrderEight.classification_of_card_eight hP with
    hcyc | hexp | hC | hD | hQ
  · exact (hnc hcyc).elim
  · have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hexp x)
    norm_num [hx4] at hd
  · obtain ⟨eC⟩ := hC
    exact (not_solvable_of_nontrivial_radicalFree hrad
      (Conjecture55OddComplement.isSolvable_of_c4c2_sylow P eC)).elim
  · exact hD
  · obtain ⟨eQ⟩ := hQ
    have hle := Conjecture55OrderEight.card_le_two_of_embedding_quaternion
      (eQ.toMonoidHom.comp f) (eQ.injective.comp hf) hsq
    omega

theorem radicalFree_sylow_four_dihedral
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {m : ℕ} (hm : Odd m) (P : Sylow 2 G) (hcard : Nat.card G = 4 * m) :
    Nonempty (P ≃* DihedralGroup 2) := by
  obtain ⟨E, hE, hsq⟩ := klein_four_of_radicalFree hrad
  obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
  exact dihedral_of_card_four_not_cyclic
    (by simpa using sylow_card_of_two_part P 2 m hm hcard)
    (not_isCyclic_of_card_four_exponent_two_embedding hE hsq f hf)

#print axioms radicalFree_sylow_eight_dihedral
#print axioms radicalFree_sylow_four_dihedral
end Conjecture55DirectSmallSylow
