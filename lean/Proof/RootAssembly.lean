/-
Copyright 2026 Contributors to this repository.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

import StructuralAssembly
import ElementaryRoots
import FrobeniusBridge
import RootShape

/-!
# Assemble the root-count route to the exact FC lower bound

The simple-group Klein-four and small-dihedral classification inputs, Frobenius
root divisibility, and the exact-root subgroup theorem remain explicit arguments.
No comparison bijection or Amiri comparison input is assumed.
-/

namespace Conjecture55RootAssembly
open Conjecture55Lean4Web Conjecture55Assembly
open Conjecture55SylowReduction

/-- Derive the full nonsolvable lower bound using actual root estimates and the
existing structural reductions, under four explicitly stated external inputs. -/
theorem lower_bound_of_four_root_structural_inputs
    (hV4 : SimpleKleinFourInput) (hclassification : SimpleDihedralInput)
    (hdiv : Conjecture55Frobenius.RootDivisibilityInput.{0})
    (hexact : Conjecture55Frobenius.ExactRootSubgroupInput.{0}) :
    NonSolvableLowerBound := by
  classical
  apply lower_bound_of_radicalFree_case
  intro G _ _ hrad hns
  by_contra hbound
  have hlt : cyc G < 2 ^ (numPrimeFactors G + 2) := Nat.lt_of_not_ge hbound
  have hnt : Nontrivial G := by
    by_contra h
    let : Subsingleton G := not_nontrivial_iff_subsingleton.mp h
    exact hns inferInstance
  let : Nontrivial G := hnt
  obtain ⟨E, hE, hEpow⟩ :=
    Conjecture55RadicalV4.exists_card_four_exponent_two_of_radicalFree hrad hV4
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := G)).ne'
  have ha : 2 ≤ a := two_le_exponent_of_four_dvd a m hm (by
    have hd := E.card_subgroup_dvd_card
    rwa [hE, hcard] at hd)
  have hbase : ∀ n, n ∣ Nat.card G → n ≤ Nat.card {x : G // x ^ n = 1} :=
    fun n hn => Conjecture55Frobenius.root_lower_bound_of_divisibility hdiv n hn
  have hdouble := Conjecture55Frobenius.double_root_bounds_of_klein_four
    hdiv hexact a m hm hcard E hE hEpow
  have hcount : 2 * a * m.divisors.card ≤ cyc G :=
    RootWeights.cyclic_count_ge_two_mul_exponent_mul_divisors
      (by omega) hm hcard hbase hdouble
  have hshape := Conjecture55RootShape.order_shape_of_divisor_count_lower_bound
    a m ha hm hcard hcount hlt
  have hshape' : (a = 2 ∧ ∀ r, m.factorization r ≤ 2) ∨ (a = 3 ∧ Squarefree m) :=
    hshape.imp (fun h => ⟨h.1, h.2.1⟩) id
  have ha23 : a = 2 ∨ a = 3 := hshape.imp And.left And.left
  have h16 : ¬16 ∣ Nat.card G := by
    rw [hcard]
    exact not_sixteen_dvd_of_small_shape a m hm ha23
  let P : Sylow 2 G := default
  have hP : Nonempty (P ≃* DihedralGroup 2) ∨ Nonempty (P ≃* DihedralGroup 4) := by
    obtain ⟨f, hf⟩ := exists_injective_to_sylow_of_card_four P E hE
    have hnc := not_isCyclic_of_card_four_exponent_two_embedding hE hEpow f hf
    rcases hshape with ⟨ha2, _, _⟩ | ⟨ha3, hsf⟩
    · exact Or.inl (dihedral_of_card_four_not_cyclic
        (by simpa [ha2] using sylow_card_of_two_part P a m hm hcard) hnc)
    · have hc8 : Nat.card P = 8 := by
        simpa [ha3] using sylow_card_of_two_part P a m hm hcard
      rcases Conjecture55OrderEight.classification_of_card_eight hc8 with
        hc | hexp | hC | hd | hQ
      · exact False.elim (hnc hc)
      · have hno4 : ∀ x : G, ¬ 4 ∣ orderOf x :=
          CyclicSum.not_four_dvd_orderOf_of_sylow_exponent_two P hexp
        have hcount8 : 8 * m.divisors.card ≤ cyc G :=
          RootWeights.cyclic_count_ge_eight_mul_divisors_of_root_bounds
            (by omega) hm hcard hbase hno4
        have hb := Conjecture55RootShape.threshold_le_of_eight_mul_divisor_count
          a m (by omega) hm hcard hcount8
        exact False.elim (Nat.not_lt_of_ge hb hlt)
      · obtain ⟨eC⟩ := hC
        exact False.elim (hns (Conjecture55C4C2.isSolvable_of_c4c2_sylow_of_squarefree_index
          P eC (by rwa [sylow_index_of_two_part P a m hm hcard])))
      · exact Or.inr hd
      · obtain ⟨eQ⟩ := hQ
        have hle := Conjecture55OrderEight.card_le_two_of_embedding_quaternion
          (eQ.toMonoidHom.comp f) (eQ.injective.comp hf) hEpow
        omega
  obtain ⟨S, hSn, hSs, hSnc, hC⟩ :=
    Conjecture55Socle.exists_simple_normal_centralizer_eq_bot hrad h16
      (four_dvd_of_simple_klein_four_input hV4)
  let : S.Normal := hSn
  obtain ⟨F, hF, hFpow⟩ := hV4 S hSs hSnc
  let Q : Sylow 2 S := default
  have hQ := Conjecture55SubgroupSylow.sylow_dihedral_of_contains_card_four_exponent_two
    P hP S F hF hFpow Q
  rcases hclassification S hSs hSnc Q hQ with hA7 | ⟨p, f, hp, hpodd, hpq, hmodel⟩
  · obtain ⟨eA7⟩ := hA7
    exact AlternatingSeven.no_embedding_of_small_shape a m hm hcard
      (hshape.imp And.left id) (S.subtype.comp eA7.symm.toMonoidHom)
      (S.subtype_injective.comp eA7.symm.injective)
  · let : Fact p.Prime := hp
    have hf : 1 ≤ f := by
      by_contra h
      have hf0 : f = 0 := by omega
      simp [hf0] at hpq
    obtain ⟨emodel⟩ := hmodel
    have hb := Conjecture55PrimePowerCase.threshold_le_of_normal_galoisField_psl2_trivial_centralizer
      p f a m hpodd hf hpq hm hcard hshape' S emodel.symm hC
    exact Nat.not_lt_of_ge hb hlt

/-- The exact affirmative FC statement follows from the four displayed inputs.
This is a conditional theorem; none of the four inputs is silently discharged. -/
theorem affirmative_target_of_four_root_structural_inputs
    (hV4 : SimpleKleinFourInput) (hclassification : SimpleDihedralInput)
    (hdiv : Conjecture55Frobenius.RootDivisibilityInput.{0})
    (hexact : Conjecture55Frobenius.ExactRootSubgroupInput.{0}) :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  affirmative_target_of_lower_bound
    (lower_bound_of_four_root_structural_inputs hV4 hclassification hdiv hexact)

#print axioms lower_bound_of_four_root_structural_inputs
#print axioms affirmative_target_of_four_root_structural_inputs

end Conjecture55RootAssembly
