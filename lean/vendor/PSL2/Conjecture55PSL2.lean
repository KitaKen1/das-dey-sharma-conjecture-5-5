import BenderSuzuki.External.Huppert.II.theorem_8_3_split
import SylowLowerBound
import Mathlib.Tactic

/-! Specializations of the audited Qiuzhen-CFSG torus construction to prime fields.
Source pin and copied-module hashes are recorded in provenance.json.
-/

namespace Conjecture55PSL2

open BenderSuzuki.MatrixGroups
open BenderSuzuki.External

abbrev PSL2 (p : ℕ) [Fact p.Prime] := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)

lemma prime_sub_one_gcd_two {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.gcd (p - 1) 2 = 2 := by
  have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out : p.Prime)).resolve_left (by omega)
  have hdiv : 2 ∣ p - 1 := by omega
  exact Nat.gcd_eq_right_iff_dvd.mpr hdiv

lemma card_psl2_mul_two {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.card (PSL2 p) * 2 = p * (p ^ 2 - 1) := by
  letI : Fact (2 < p) := ⟨by omega⟩
  have hcenter := huppert614_card_center_of_neg_one_ne_one (K := ZMod p) ZMod.neg_one_ne_one
  have hcard := huppert614_card_psl_mul_center (K := ZMod p)
  simpa only [PSL2, hcenter, Nat.card_zmod] using hcard

lemma card_psl2 {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.card (PSL2 p) = p * (p ^ 2 - 1) / 2 := by
  have h := card_psl2_mul_two hp
  omega

lemma exists_split_torus {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ U : Subgroup (PSL2 p), IsCyclic U ∧ Nat.card U = (p - 1) / 2 ∧
      Nat.card (Subgroup.normalizer (U : Set (PSL2 p))) = p - 1 := by
  obtain ⟨U, hcyc, hcard, hnorm⟩ :=
    huppert_II_8_3_split_torus_normalizer_card (F := ZMod p) (p := p) (f := 1) (by simp)
  have hcard' : Nat.card U = (p - 1) / 2 := by
    simpa only [Nat.card_zmod, prime_sub_one_gcd_two hp] using hcard
  have hU : U ≠ ⊥ := by
    intro h
    have hbad : Nat.card U = 1 := by simp [h]
    omega
  refine ⟨U, hcyc, hcard', ?_⟩
  have hnorm' := hnorm U le_rfl hU
  have hgcd := prime_sub_one_gcd_two hp
  have hdiv : 2 ∣ p - 1 := Nat.gcd_eq_right_iff_dvd.mp hgcd
  rw [hnorm', hcard', Nat.mul_comm, Nat.div_mul_cancel hdiv]

lemma exists_nonsplit_torus {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ S : Subgroup (PSL2 p), IsCyclic S ∧ Nat.card S = (p + 1) / 2 ∧
      Nat.card (Subgroup.normalizer (S : Set (PSL2 p))) = p + 1 := by
  obtain ⟨S, hcyc, hcard, hnorm⟩ :=
    huppert_II_8_4_nonsplit_torus_normalizer_card (F := ZMod p) (p := p) (f := 1) (by simp)
  have hcard' : Nat.card S = (p + 1) / 2 := by
    simpa only [Nat.card_zmod, prime_sub_one_gcd_two hp] using hcard
  refine ⟨S, hcyc, hcard', ?_⟩
  have hgcd := prime_sub_one_gcd_two hp
  have hdiv : 2 ∣ p - 1 := Nat.gcd_eq_right_iff_dvd.mp hgcd
  have hdiv' : 2 ∣ p + 1 := by omega
  rw [hnorm, hcard', Nat.mul_comm, Nat.div_mul_cancel hdiv']

lemma exists_split_torus_data {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ U : Subgroup (PSL2 p), IsCyclic U ∧ Nat.card U = (p - 1) / 2 ∧
      Nat.card (Subgroup.normalizer (U : Set (PSL2 p))) = 2 * Nat.card U := by
  obtain ⟨U, hcyc, hcard, hnorm⟩ := exists_split_torus hp
  refine ⟨U, hcyc, hcard, ?_⟩
  have hdiv : 2 ∣ p - 1 := Nat.gcd_eq_right_iff_dvd.mp (prime_sub_one_gcd_two hp)
  rw [hnorm, hcard, Nat.mul_comm, Nat.div_mul_cancel hdiv]

lemma exists_nonsplit_torus_data {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ S : Subgroup (PSL2 p), IsCyclic S ∧ Nat.card S = (p + 1) / 2 ∧
      Nat.card (Subgroup.normalizer (S : Set (PSL2 p))) = 2 * Nat.card S := by
  obtain ⟨S, hcyc, hcard, hnorm⟩ := exists_nonsplit_torus hp
  refine ⟨S, hcyc, hcard, ?_⟩
  have hdiv : 2 ∣ p - 1 := Nat.gcd_eq_right_iff_dvd.mp (prime_sub_one_gcd_two hp)
  have hdiv' : 2 ∣ p + 1 := by omega
  rw [hnorm, hcard, Nat.mul_comm, Nat.div_mul_cancel hdiv']

lemma sylow_cyclic_card {p : ℕ} [Fact p.Prime] (P : Sylow p (PSL2 p)) :
    IsCyclic P ∧ Nat.card P = p := by
  obtain ⟨e⟩ := huppert_II_8_2_a_sylow_equiv_additive
    (F := ZMod p) (p := p) (f := 1) (by simp) P
  have hcyc : IsCyclic (Multiplicative (ZMod p)) := inferInstance
  refine ⟨e.isCyclic.mp hcyc, ?_⟩
  simpa using (Nat.card_congr e.toEquiv).symm

lemma sylow_card_lower_bound {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    p + 1 ≤ Nat.card (Sylow p (PSL2 p)) := by
  letI : IsSimpleGroup (PSL2 p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (F := ZMod p) (by simpa using (show 4 ≤ p by omega))
  apply sylow_count_lower_bound (p := p) ?_ (fun P => (sylow_cyclic_card P).2)
  have hcard := card_psl2_mul_two hp
  have hsq : 3 ≤ p ^ 2 - 1 := by
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  nlinarith [Nat.mul_le_mul_left p hsq]

#print axioms exists_split_torus_data
#print axioms exists_nonsplit_torus_data
#print axioms sylow_card_lower_bound
#print axioms card_psl2_mul_two
#print axioms card_psl2
#print axioms exists_split_torus
#print axioms exists_nonsplit_torus
#print axioms sylow_cyclic_card

#print axioms BenderSuzuki.External.huppert_II_8_3_split_torus_normalizer_card
#print axioms BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_normalizer_card
#print axioms BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive

end Conjecture55PSL2
