import Order16Candidates
import CompletedBounds
import C8C2Case

/-! Application to the exact Formal Conjectures definitions of `cyc` and
`numPrimeFactors`. Ordinary Frobenius divisibility is supplied by its proof.
The Klein-four subgroup is an explicit object, not an assumed classification. -/
namespace Conjecture55OrderSixteen
open Smallgroups.UsefulTheorems Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55FrobeniusProof Conjecture55SylowReduction

/-- The strict FC bound forces a noncyclic Sylow group of order sixteen
into five concrete isomorphism types. -/
theorem counterexample_sylow16_candidates
    {G : Type*} [Group G] [Fintype G] {m : ℕ} (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P)
    (hcard : Nat.card G = 16 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ∃ i : Fin 14, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) ∧
      Nonempty (P ≃* order16_wild_reps i) := by
  have hc : Nat.card G = 2 ^ 4 * m := by simpa using hcard
  have hP : Nat.card P = 16 := by
    simpa using RootWeights.sylow_card_eq_two_part P hm hc
  obtain ⟨x, hx⟩ := RootWeights.exists_order_half_sylow_card_of_strict_fc_bound
    (by decide : 3 ≤ 4) hm P hnc hc (rootCountLowerBound G) hlt
  exact classification_of_order8 hP hnc x (by simpa using hx)

/-- An actual Klein-four subgroup reduces the order-sixteen branch to
C8 × C2, SD16, M16 or D16. It also forces the odd part to be squarefree.
These four types are still candidates, not counterexamples or exclusions. -/
theorem counterexample_sylow16_candidates_of_klein
    {G : Type*} [Group G] [Fintype G] {m : ℕ} (hm : Odd m)
    (P : Sylow 2 G) (hcard : Nat.card G = 16 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2))
    (E : Subgroup G) (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    Squarefree m ∧ ∃ i : Fin 14, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) ∧
      Nonempty (P ≃* order16_wild_reps i) := by
  obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
  have hnc := not_isCyclic_of_card_four_exponent_two_embedding hE hsq f hf
  have hc : Nat.card G = 2 ^ 4 * m := by simpa using hcard
  have hP : Nat.card P = 16 := by
    simpa using RootWeights.sylow_card_eq_two_part P hm hc
  have hsf : Squarefree m := by
    have hshape := Conjecture55CompletedBounds.counterexample_order_shape
      (by decide : 2 ≤ 4) hm P hnc hc hlt
    rcases hshape with ⟨ha, _, _⟩ | ⟨_, hsf⟩
    · norm_num at ha
    · exact hsf
  obtain ⟨x, hx⟩ := RootWeights.exists_order_half_sylow_card_of_strict_fc_bound
    (by decide : 3 ≤ 4) hm P hnc hc (rootCountLowerBound G) hlt
  exact ⟨hsf, classification_of_order8_of_klein_embedding hP hnc x
    (by simpa using hx) f hf hE hsq⟩

/-- For a nonsolvable FC candidate containing a Klein-four subgroup, the
Sylow order-16 branch reduces to SD16, M16 or Mathlib's D16.
Both the cyclic and C8 × C2 possibilities, as well as Q16, have been removed. -/
theorem nonsolvable_sylow16_three_cases
    {G : Type*} [Group G] [Fintype G] {m : ℕ} (hm : Odd m)
    (P : Sylow 2 G) (hcard : Nat.card G = 16 * m)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) (hns : ¬ Group.IsSolvable G)
    (E : Subgroup G) (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    Squarefree m ∧ (Nonempty (P ≃* order16_wild_G2) ∨
      Nonempty (P ≃* order16_wild_G3) ∨ Nonempty (P ≃* DihedralGroup 8)) := by
  obtain ⟨hsf, i, hi, ⟨e⟩⟩ :=
    counterexample_sylow16_candidates_of_klein hm P hcard hlt E hE hsq
  refine ⟨hsf, ?_⟩
  rcases hi with rfl | rfl | rfl | rfl
  · have ec : P ≃* Multiplicative Conjecture55C8C2.A :=
      e.trans (MulEquiv.prodMultiplicative (ZMod 8) (ZMod 2)).symm
    have hindex : P.index = m := sylow_index_of_two_part P 4 m hm (by simpa using hcard)
    exact (hns (Conjecture55C8C2.isSolvable_of_c8c2_sylow_of_squarefree_index P ec
      (hindex.symm ▸ hsf))).elim
  · exact Or.inl ⟨e⟩
  · exact Or.inr (Or.inl ⟨e⟩)
  · exact Or.inr (Or.inr ⟨e.trans dihedral16Equiv⟩)

#print axioms nonsolvable_sylow16_three_cases
#print axioms counterexample_sylow16_candidates
#print axioms counterexample_sylow16_candidates_of_klein
end Conjecture55OrderSixteen
