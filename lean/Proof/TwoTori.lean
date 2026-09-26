import FieldTransport
import Families

/-! Two actual torus conjugacy families provide a quadratic cyclic-subgroup
lower bound over every odd Galois field of order at least five. -/

namespace Conjecture55SquareField
noncomputable section

open BenderSuzuki.External

theorem cyclic_count_ge_two_families
    {G : Type*} [Group G] [Finite G]
    (U V : Subgroup G) (hU : IsCyclic U) (hV : IsCyclic V)
    (hUV : Nat.card U ≠ Nat.card V) :
    (Subgroup.normalizer (U : Set G)).index +
      (Subgroup.normalizer (V : Set G)).index ≤
      Nat.card (CyclicSum.CyclicSubgroups G) := by
  let fU := CyclicSum.conjugateFamilyToCyclic U hU
  let fV := CyclicSum.conjugateFamilyToCyclic V hV
  have hUi : Function.Injective fU := fun _ _ h =>
    Subtype.ext (congrArg (fun C : CyclicSum.CyclicSubgroups G => C.val) h)
  have hVi : Function.Injective fV := fun _ _ h =>
    Subtype.ext (congrArg (fun C : CyclicSum.CyclicSubgroups G => C.val) h)
  have hUVne (u : CyclicSum.ConjugateFamily U) (v : CyclicSum.ConjugateFamily V) :
      fU u ≠ fV v := by
    intro heq
    have hc := congrArg (fun C : CyclicSum.CyclicSubgroups G => Nat.card C.1) heq
    have hu : Nat.card (fU u).1 = Nat.card U :=
      CyclicSum.conjugate_family_subgroup_card U u
    have hv : Nat.card (fV v).1 = Nat.card V :=
      CyclicSum.conjugate_family_subgroup_card V v
    exact hUV (hu.symm.trans (hc.trans hv))
  have hcount := Nat.card_le_card_of_injective _ (hUi.sumElim hVi hUVne)
  simpa only [Nat.card_sum, CyclicSum.conjugate_family_card] using hcount

theorem cyclic_count_ge_square_of_two_tori
    {G : Type*} [Group G] [Finite G] (q : ℕ) (hqodd : Odd q) (hq5 : 5 ≤ q)
    (U V : Subgroup G) (hU : IsCyclic U) (hV : IsCyclic V)
    (hUcard : Nat.card U = (q - 1) / 2)
    (hVcard : Nat.card V = (q + 1) / 2)
    (hUN : Nat.card (Subgroup.normalizer (U : Set G)) = 2 * Nat.card U)
    (hVN : Nat.card (Subgroup.normalizer (V : Set G)) = 2 * Nat.card V)
    (hGcard : Nat.card G = q * (q ^ 2 - 1) / 2) :
    q ^ 2 ≤ Nat.card (CyclicSum.CyclicSubgroups G) := by
  have hpodd : q % 2 = 1 := Nat.odd_iff.mp hqodd
  have hu : 2 * Nat.card U + 1 = q := by omega
  have hv : 2 * Nat.card V = q + 1 := by omega
  have huv : Nat.card V = Nat.card U + 1 := by omega
  have hsum : Nat.card U + Nat.card V = q := by omega
  have hsq : q ^ 2 - 1 = 4 * Nat.card U * Nat.card V := by
    have heq : q ^ 2 = 4 * Nat.card U * Nat.card V + 1 := by
      rw [← hu, huv]
      ring
    omega
  have hGfact : Nat.card G = (2 * Nat.card U) * (q * Nat.card V) := by
    calc
      Nat.card G = ((2 * Nat.card U) * (q * Nat.card V) * 2) / 2 := by
        rw [hGcard, hsq]
        congr 1
        ring
      _ = _ := by simp
  have hiU : (Subgroup.normalizer (U : Set G)).index = q * Nat.card V := by
    apply Nat.eq_of_mul_eq_mul_right (m := 2 * Nat.card U) (by omega)
    have heq := (Subgroup.normalizer (U : Set G)).index_mul_card
    rw [hUN, hGfact] at heq
    simpa only [mul_comm] using heq
  have hiV : (Subgroup.normalizer (V : Set G)).index = q * Nat.card U := by
    apply Nat.eq_of_mul_eq_mul_right (m := 2 * Nat.card V) (by omega)
    have heq := (Subgroup.normalizer (V : Set G)).index_mul_card
    rw [hVN, hGfact] at heq
    convert heq using 1 <;> ring
  have hindices : (Subgroup.normalizer (U : Set G)).index +
      (Subgroup.normalizer (V : Set G)).index = q ^ 2 := by
    rw [hiU, hiV, ← Nat.mul_add]
    rw [Nat.add_comm (Nat.card V), hsum]
    ring
  have hc := cyclic_count_ge_two_families U V hU hV (by omega)
  omega

theorem exists_two_tori_galoisField
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f) :
    ∃ U V : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)),
      IsCyclic U ∧ IsCyclic V ∧
      Nat.card U = (p ^ f - 1) / 2 ∧ Nat.card V = (p ^ f + 1) / 2 ∧
      Nat.card (Subgroup.normalizer (U : Set
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)))) = 2 * Nat.card U ∧
      Nat.card (Subgroup.normalizer (V : Set
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)))) = 2 * Nat.card V := by
  have hFcard := GaloisField.card p f (by omega)
  have hodd : Odd (p ^ f) := hpodd.pow
  have htwo : 2 ∣ p ^ f - 1 := by
    have hmod := Nat.odd_iff.mp hodd
    omega
  have hgcd : Nat.gcd (p ^ f - 1) 2 = 2 := Nat.gcd_eq_right_iff_dvd.mpr htwo
  obtain ⟨U, hUcyc, hUc, hUN⟩ :=
    huppert_II_8_3_split_torus_normalizer_card hFcard
  obtain ⟨V, hVcyc, hVc, hVN⟩ :=
    huppert_II_8_4_nonsplit_torus_normalizer_card hFcard
  have hUc' : Nat.card U = (p ^ f - 1) / 2 := by
    simpa only [hFcard, hgcd] using hUc
  have hVc' : Nat.card V = (p ^ f + 1) / 2 := by
    simpa only [hFcard, hgcd] using hVc
  have hUne : U ≠ ⊥ := by
    intro he
    have hc : Nat.card U = 1 := by simp [he]
    omega
  exact ⟨U, V, hUcyc, hVcyc, hUc', hVc', hUN U le_rfl hUne, hVN⟩

theorem psl2_galoisField_cyclic_count_ge_square
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f) :
    (p ^ f) ^ 2 ≤ Nat.card (CyclicSum.CyclicSubgroups
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f))) := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUN, hVN⟩ :=
    exists_two_tori_galoisField p f hpodd hf hq
  exact cyclic_count_ge_square_of_two_tori (p ^ f) hpodd.pow hq U V hU hV
    hUc hVc hUN hVN (Conjecture55FieldTransport.card_psl2_galoisField p f hpodd hf)

end
end Conjecture55SquareField

#print axioms Conjecture55SquareField.cyclic_count_ge_two_families
#print axioms Conjecture55SquareField.cyclic_count_ge_square_of_two_tori
#print axioms Conjecture55SquareField.exists_two_tori_galoisField
#print axioms Conjecture55SquareField.psl2_galoisField_cyclic_count_ge_square
