import SylowReduction
import RadicalV4
import PrimePowerCase
import SubgroupSylow

/-! An explicit assembly boundary for the remaining deep group-theory inputs. -/
namespace Conjecture55Assembly
open Conjecture55Lean4Web

/-- The precise simple-group Klein-four input needed by the reductions. -/
def SimpleKleinFourInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ¬IsMulCommutative S →
    ∃ E : Subgroup S, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1

/-- The needed order-divisibility bijection, stated with concrete cyclic factors. -/
def ComparisonInput : Prop :=
  ∀ (G : Type) [Group G] [Fintype G],
    (∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1) →
    ∀ a m : ℕ, 2 ≤ a → Odd m → Nat.card G = 2 ^ a * m →
      ∃ e : G ≃ Multiplicative (ZMod (2 ^ (a - 1) * m)) × Multiplicative (ZMod 2),
        ∀ x : G, orderOf x ∣ orderOf (e x)

/-- Only the small-dihedral simple-group classification is needed here. -/
def SimpleDihedralInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ¬IsMulCommutative S →
    ∀ P : Sylow 2 S,
      (Nonempty (P ≃* DihedralGroup 2) ∨ Nonempty (P ≃* DihedralGroup 4)) →
      Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ f ∧
          Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f))

/-- A Klein-four subgroup supplies the divisibility hypothesis in the socle reduction. -/
theorem four_dvd_of_simple_klein_four_input
    (hV4 : SimpleKleinFourInput) (S : Type) [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hn : ¬IsMulCommutative S) : 4 ∣ Nat.card S := by
  obtain ⟨E, hE, -⟩ := hV4 S hs hn
  exact hE ▸ E.card_subgroup_dvd_card

theorem two_le_exponent_of_four_dvd (a m : ℕ) (hm : Odd m)
    (hd : 4 ∣ 2 ^ a * m) : 2 ≤ a := by
  by_contra ha
  have ha01 : a = 0 ∨ a = 1 := by omega
  have hodd := Nat.odd_iff.mp hm
  rcases ha01 with rfl | rfl <;> norm_num at hd <;> omega

theorem not_sixteen_dvd_of_small_shape (a m : ℕ) (hm : Odd m)
    (ha : a = 2 ∨ a = 3) : ¬ 16 ∣ 2 ^ a * m := by
  intro hd
  have hodd := Nat.odd_iff.mp hm
  rcases ha with rfl | rfl <;> norm_num at hd <;> omega

/-- Assemble the genuine reductions under exactly three named external inputs.
None of these inputs is discharged by this conditional theorem. -/
theorem lower_bound_of_three_structural_inputs
    (hV4 : SimpleKleinFourInput) (hcomparison : ComparisonInput)
    (hclassification : SimpleDihedralInput) : NonSolvableLowerBound := by
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
  let : NeZero (2 ^ (a - 1) * m) := ⟨by have := hm.pos; positivity⟩
  obtain ⟨e, he⟩ := hcomparison G ⟨E, hE, hEpow⟩ a m ha hm hcard
  have hK : Nat.card (Multiplicative (ZMod (2 ^ (a - 1) * m))) =
      2 ^ (a - 1) * m := by simp
  have hH : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
  have hshape := OrderShape.order_shape_of_comparison a m ha hm hK hH e he hlt
  have hshape' : (a = 2 ∧ ∀ r, m.factorization r ≤ 2) ∨ (a = 3 ∧ Squarefree m) :=
    hshape.imp (fun h => ⟨h.1, h.2.1⟩) id
  have ha23 : a = 2 ∨ a = 3 := hshape.imp And.left And.left
  have h16 : ¬16 ∣ Nat.card G := by
    rw [hcard]
    exact not_sixteen_dvd_of_small_shape a m hm ha23
  let P : Sylow 2 G := default
  have hP := Conjecture55SylowReduction.dihedral_sylow_of_cyclic_comparison
    a m ha hm hK hH e he hlt hns P E hE hEpow
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

/-- The requested affirmative statement follows once the three displayed structural inputs
are proved. This theorem is conditional, and is not the completed FC target. -/
theorem affirmative_target_of_three_structural_inputs
    (hV4 : SimpleKleinFourInput) (hcomparison : ComparisonInput)
    (hclassification : SimpleDihedralInput) :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  affirmative_target_of_lower_bound
    (lower_bound_of_three_structural_inputs hV4 hcomparison hclassification)

#print axioms lower_bound_of_three_structural_inputs
#print axioms affirmative_target_of_three_structural_inputs
#print axioms four_dvd_of_simple_klein_four_input
#print axioms two_le_exponent_of_four_dvd
#print axioms not_sixteen_dvd_of_small_shape
end Conjecture55Assembly
