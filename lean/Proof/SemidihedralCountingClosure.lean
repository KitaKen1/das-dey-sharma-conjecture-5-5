import EmbeddedChainCount
import CharacteristicChainCount
import GWStructuralInput
import DirectSylowAlternatives

/-! Close the two semidihedral branches by conjugate counting, without a
semidihedral simple-group classification or an Amiri comparison theorem. -/
namespace Conjecture55CountingClosure
open Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55NormalCyclicChain Conjecture55EmbeddedChain
open Conjecture55CharacteristicChain Conjecture55CharacteristicCount
open Conjecture55OddSquarefree Conjecture55DirectSylow Conjecture55CounterexampleModels
open Smallgroups.UsefulTheorems Conjecture55OrderThirtyTwo
noncomputable section

theorem bound_contradicts_strict_threshold {G : Type*} [Group G] [Fintype G]
    {a m : ℕ} (ha : 0 < a) (hm : Odd m) (hsf : Squarefree m)
    (hG : Nat.card G = 2 ^ a * m)
    (hbound : 17 * m.divisors.card ≤ 2 * cyc G)
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) : False := by
  have hω : numPrimeFactors G = m.primeFactors.card + 1 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card]
    rw [hG]
    exact card_primeFactors_prime_pow_mul_of_not_dvd 2 a m Nat.prime_two
      ha hm.pos hm.not_two_dvd_nat
  have hexp : 2 ^ (numPrimeFactors G + 2) = 8 * m.divisors.card := by
    rw [hω, divisors_card_of_squarefree hsf,
      show m.primeFactors.card + 1 + 2 = m.primeFactors.card + 3 by omega, pow_add]
    ring
  rw [hexp] at hlt
  omega

theorem exclude_model {G M : Type*} [Group G] [Fintype G] [Group M] [Finite M]
    {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m) (hsf : Squarefree m)
    (hG : Nat.card G = 2 ^ a * m) (hM : Nat.card M = 2 ^ a)
    (S : Subgroup G) (hs : IsSimpleGroup S) (hn : ¬IsMulCommutative S)
    (Q : Sylow 2 S) (e : Q ≃* M)
    (hchain : ∃ B : Fin 3 → Subgroup M, (∀ i, IsCyclic (B i)) ∧
      (∀ i, Nat.card (B i) = 2 ^ (i.val + 1)) ∧ (∀ i, (B i).Normal))
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) : False := by
  obtain ⟨B, hcyc, hcard, hnorm⟩ := hchain
  let f : M →* G := S.subtype.comp ((Q : Subgroup S).subtype.comp e.symm.toMonoidHom)
  have hf : Function.Injective f := S.subtype_injective.comp
    ((Q : Subgroup S).subtype_injective.comp e.symm.injective)
  have hfS : f.range ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact (e.symm x).val.property
  have h4 : 4 ∣ Nat.card S := by
    have hQ : Nat.card Q = 2 ^ a := (Nat.card_congr e.toEquiv).trans hM
    exact ((pow_dvd_pow 2 ha).trans hQ.symm.dvd).trans
      (Q : Subgroup S).card_subgroup_dvd_card
  have hbound := count_of_embedded_chain hm hsf hG hM S hs hn h4 f hf hfS
    B hcyc hcard hnorm
  exact bound_contradicts_strict_threshold (by omega) hm hsf hG hbound hlt

/-- A dihedral Sylow subgroup of the simple normal subgroup with order at
least `16` is excluded directly by its characteristic rotation chain.  This
does not use the Gorenstein--Walter classification. -/
theorem exclude_large_dihedral
    {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    {a m l : ℕ}
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hm : Odd m) (P : Sylow 2 G) (hG : Nat.card G = 2 ^ a * m)
    (S : Subgroup G) (hSn : S.Normal) (hs : IsSimpleGroup S)
    (hn : ¬IsMulCommutative S) (Q : Sylow 2 S)
    (hl : 3 ≤ l) (eQ : Q ≃* DihedralGroup (2 ^ l))
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) : False := by
  have hQcard : Nat.card Q = 2 ^ (l + 1) := by
    calc
      Nat.card Q = Nat.card (DihedralGroup (2 ^ l)) := Nat.card_congr eQ.toEquiv
      _ = 2 * 2 ^ l := DihedralGroup.nat_card
      _ = 2 ^ (l + 1) := by rw [pow_succ']
  obtain ⟨i, hi⟩ :=
    Conjecture55SubgroupSylow.exists_injective_hom_to_ambient_sylow 2 P S Q
  have hdiv : Nat.card Q ∣ Nat.card P := Subgroup.card_dvd_of_injective i hi
  have hPcard : Nat.card P = 2 ^ a := RootWeights.sylow_card_eq_two_part P hm hG
  have hla : l + 1 ≤ a := by
    rw [hQcard, hPcard] at hdiv
    exact (Nat.pow_dvd_pow_iff_le_right Nat.prime_two.one_lt).mp hdiv
  have ha4 : 4 ≤ a := by omega
  have hsf : Squarefree m :=
    squarefree_of_four_le_two_part hrad ha4 hm P hG hlt
  have h4 : 4 ∣ Nat.card S := by
    have h4Q : 4 ∣ Nat.card Q := by
      rw [hQcard]
      exact pow_dvd_pow 2 (by omega : 2 ≤ l + 1)
    exact h4Q.trans (Q : Subgroup S).card_subgroup_dvd_card
  obtain ⟨D, hDcyc, hDcard, hDchar⟩ := dihedral_characteristic_chain hl
  let B (j : Fin 3) : Subgroup Q := (D j).map eQ.symm.toMonoidHom
  have hBcyc (j : Fin 3) : IsCyclic (B j) := by
    letI : IsCyclic (D j) := hDcyc j
    exact (cyclicSubgroupMap eQ.symm.toMonoidHom ⟨D j, inferInstance⟩).2
  have hBcard (j : Fin 3) : Nat.card (B j) = 2 ^ (j.val + 1) :=
    (Subgroup.card_map_of_injective eQ.symm.injective).trans (hDcard j)
  have hBchar (j : Fin 3) : (B j).Characteristic := by
    letI : (D j).Characteristic := hDchar j
    exact characteristic_map_mulEquiv (D j) eQ.symm
  have hbound := count_of_characteristic_chain_in_normal_subgroup
    hm hsf hG S hSn hs hn h4 Q B hBcyc hBcard hBchar
  exact bound_contradicts_strict_threshold (by omega) hm hsf hG hbound hlt

theorem radicalFree_lower_bound (G : Type) [Group G] [Fintype G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hns : ¬Group.IsSolvable G) : 2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  classical
  by_contra hbound
  have hlt := Nat.lt_of_not_ge hbound
  have hnt : Nontrivial G := by
    by_contra h
    let : Subsingleton G := not_nontrivial_iff_subsingleton.mp h
    exact hns inferInstance
  let : Nontrivial G := hnt
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := G)).ne'
  let P : Sylow 2 G := default
  obtain ⟨S, hSn, hSs, hSc, hC, hQall⟩ :=
    simple_normal_alternatives hrad hm P hcard hlt
  let : S.Normal := hSn
  let Q : Sylow 2 S := default
  rcases hQall Q with ⟨l, hl, hl4, ⟨eQ⟩⟩ | ⟨ha, hsf, ⟨eQ⟩⟩ | ⟨ha, hsf, ⟨eQ⟩⟩
  · by_cases hlarge : 3 ≤ l
    · exact exclude_large_dihedral hrad hm P hcard S hSn hSs hSc Q hlarge eQ hlt
    · exact not_actual_normal_model hrad hm P hcard hlt S hC
        (Conjecture55GWAdapter.simple_model_of_dihedral_sylow S hSs hSc hl Q eQ)
  · subst a
    exact exclude_model (by decide) hm hsf hcard (by
      rw [Nat.card_eq_fintype_card]; decide) S hSs hSc Q eQ sd16_chain hlt
  · subst a
    exact exclude_model (by decide) hm hsf hcard (by
      rw [Nat.card_eq_fintype_card]; decide) S hSs hSc Q eQ sd32_chain hlt

/-- The complete lower bound for all finite nonsolvable groups. -/
theorem nonsolvable_lower_bound : NonSolvableLowerBound :=
  lower_bound_of_radicalFree_case radicalFree_lower_bound

/-- The affirmative statement with exactly the FC quantifiers and strict bound. -/
theorem affirmative_target :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  affirmative_target_of_lower_bound nonsolvable_lower_bound

#print axioms bound_contradicts_strict_threshold
#print axioms exclude_model
#print axioms exclude_large_dihedral
#print axioms radicalFree_lower_bound
#print axioms nonsolvable_lower_bound
#print axioms affirmative_target
end
end Conjecture55CountingClosure
