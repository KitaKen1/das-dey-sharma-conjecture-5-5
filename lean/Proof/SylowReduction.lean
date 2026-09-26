import Conjecture55Foundation
import SmallGroups
import ComparisonSplit

/-! The actual comparison map and a Klein-four subgroup force a small dihedral Sylow group. -/

namespace Conjecture55SylowReduction
open Conjecture55Lean4Web

theorem sylow_card_of_two_part {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (a m : ℕ) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ a * m) : Nat.card P = 2 ^ a := by
  have h2 : ¬ 2 ∣ m := by simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm
  rw [P.card_eq_multiplicity, hcard,
    Nat.factorization_mul (by positivity) hm.pos.ne']
  simp [Nat.prime_two.factorization_pow, Nat.factorization_eq_zero_of_not_dvd h2]

theorem sylow_index_of_two_part {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (a m : ℕ) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ a * m) : P.index = m := by
  have hc := P.index_mul_card
  rw [sylow_card_of_two_part P a m hm hcard, hcard] at hc
  nlinarith [show 0 < 2 ^ a by positivity]

theorem exists_injective_to_sylow_of_card_four {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (E : Subgroup G) (hE : Nat.card E = 4) :
    ∃ f : E →* P, Function.Injective f := by
  have hgroup : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by simpa using hE)
  obtain ⟨Q, hQ⟩ := hgroup.exists_le_sylow
  exact ⟨(Q.equiv P).toMonoidHom.comp (Subgroup.inclusion hQ),
    (Q.equiv P).injective.comp (Subgroup.inclusion_injective hQ)⟩

theorem not_isCyclic_of_card_four_exponent_two_embedding
    {E P : Type*} [Group E] [Group P] [Finite E]
    (hE : Nat.card E = 4) (hpow : ∀ x : E, x ^ 2 = 1)
    (f : E →* P) (hf : Function.Injective f) : ¬ IsCyclic P := by
  intro hP
  let := hP
  let : IsCyclic E := isCyclic_of_injective f hf
  have hcard : Nat.card E ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
  norm_num [hE] at hcard

theorem dihedral_of_card_four_not_cyclic {P : Type*} [Group P]
    (hcard : Nat.card P = 4) (hnot : ¬ IsCyclic P) :
    Nonempty (P ≃* DihedralGroup 2) := by
  have hK : IsKleinFour P := (SylowInputs.cyclic_or_kleinFour_of_card_four hcard).resolve_left hnot
  let := hK
  exact IsKleinFour.nonempty_mulEquiv

theorem card_of_cyclic_comparison
    {G K H : Type*} [Group G] [Group K] [Group H]
    (a m : ℕ) (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (a - 1) * m) (hH : Nat.card H = 2)
    (e : G ≃ K × H) : Nat.card G = 2 ^ a * m := by
  have hpow : 2 ^ (a - 1) * 2 = 2 ^ a := by
    rw [← pow_succ]
    congr 1
    omega
  rw [Nat.card_congr e, Nat.card_prod, hK, hH]
  calc
    2 ^ (a - 1) * m * 2 = (2 ^ (a - 1) * 2) * m := by ring
    _ = 2 ^ a * m := by rw [hpow]

/-- The five order-eight possibilities are reduced using the original comparison map,
the Klein-four subgroup, and nonsolvability of the ambient counterexample. -/
theorem dihedral_sylow_of_cyclic_comparison
    {G K H : Type*} [Group G] [Group K] [Group H]
    [Fintype G] [Fintype K] [Fintype H] [IsCyclic K]
    (a m : ℕ) (ha : 2 ≤ a) (hm : Odd m)
    (hK : Nat.card K = 2 ^ (a - 1) * m) (hH : Nat.card H = 2)
    (e : G ≃ K × H) (he : ∀ x : G, orderOf x ∣ orderOf (e x))
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) (hns : ¬ Group.IsSolvable G)
    (P : Sylow 2 G) (E : Subgroup G)
    (hE : Nat.card E = 4) (hEpow : ∀ x : E, x ^ 2 = 1) :
    Nonempty (P ≃* DihedralGroup 2) ∨ Nonempty (P ≃* DihedralGroup 4) := by
  have hcard := card_of_cyclic_comparison a m (by omega) hK hH e
  obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
  have hnc := not_isCyclic_of_card_four_exponent_two_embedding hE hEpow f hf
  rcases OrderShape.order_shape_of_comparison a m ha hm hK hH e he hlt with
    ⟨ha2, _, _⟩ | ⟨ha3, hsf⟩
  · exact Or.inl (dihedral_of_card_four_not_cyclic
      (by simpa [ha2] using sylow_card_of_two_part P a m hm hcard) hnc)
  · have hc8 : Nat.card P = 8 := by
      simpa [ha3] using sylow_card_of_two_part P a m hm hcard
    rcases Conjecture55OrderEight.classification_of_card_eight hc8 with
      hc | hexp | hC | hd | hQ
    · exact False.elim (hnc hc)
    · have hbound := Conjecture55ComparisonSplit.fc_lower_bound_of_cyclic_comparison_and_sylow_exponent_two
        m hm (by simpa [ha3] using hK) hH P hexp e he
      exact False.elim (Nat.not_lt_of_ge hbound hlt)
    · obtain ⟨eC⟩ := hC
      exact False.elim (hns (Conjecture55C4C2.isSolvable_of_c4c2_sylow_of_squarefree_index
        P eC (by rwa [sylow_index_of_two_part P a m hm hcard])))
    · exact Or.inr hd
    · obtain ⟨eQ⟩ := hQ
      have hle := Conjecture55OrderEight.card_le_two_of_embedding_quaternion
        (eQ.toMonoidHom.comp f) (eQ.injective.comp hf) hEpow
      omega

#print axioms sylow_card_of_two_part
#print axioms sylow_index_of_two_part
#print axioms exists_injective_to_sylow_of_card_four
#print axioms not_isCyclic_of_card_four_exponent_two_embedding
#print axioms dihedral_of_card_four_not_cyclic
#print axioms card_of_cyclic_comparison
#print axioms dihedral_sylow_of_cyclic_comparison
end Conjecture55SylowReduction
