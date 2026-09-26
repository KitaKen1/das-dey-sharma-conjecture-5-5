import SquareFieldPSL2
import SquareFieldAut
import AlmostSimpleCase

/-! All PSL2 branches with odd-part prime exponents at most two.
The degree-two almost-simple endpoint uses the actual checked semilinear
automorphism cardinality, not an additional classification hypothesis. -/

namespace Conjecture55DegreeAtMostTwo
noncomputable section
open Conjecture55Lean4Web
open Conjecture55Lean4Web

theorem two_dvd_card_psl2_square (p : ℕ) [Fact p.Prime] (hpodd : Odd p) :
    2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2)) := by
  have hmod := PrimePower.odd_fourth_mod_sixteen p hpodd
  have h4 : 4 ∣ (p ^ 2) ^ 2 - 1 := by
    rw [← pow_mul]
    norm_num only [Nat.reduceMul]
    omega
  obtain ⟨k, hk⟩ := h4
  rw [Conjecture55FieldTransport.card_psl2_galoisField p 2 hpodd (by omega), hk]
  have he : p ^ 2 * (4 * k) / 2 = 2 * (p ^ 2 * k) := by
    rw [show p ^ 2 * (4 * k) = (2 * (p ^ 2 * k)) * 2 by ring]
    simp
  rw [he]
  exact dvd_mul_right _ _

theorem fc_threshold_le_of_square_psl2_subgroup_index_pow_two
    {G : Type*} [Group G] [Fintype G]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (S : Subgroup G)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2) ≃* S)
    (k : ℕ) (hindex : S.index = 2 ^ k) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  let H := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2)
  have hcard : Nat.card H = Nat.card S := Nat.card_congr e.toEquiv
  have h2 : 2 ∣ Nat.card S := hcard ▸ two_dvd_card_psl2_square p hpodd
  have hprimes : (Nat.card G).primeFactors = (Nat.card H).primeFactors := by
    rw [PSL2Extensions.primeFactors_eq_of_index_pow_two S h2 k hindex, hcard]
  have hb : 2 ^ ((Nat.card G).primeFactors.card + 2) ≤ cyc G := by
    rw [hprimes]
    calc
      _ ≤ cyc H := Conjecture55SquareField.psl2_square_fc_threshold_le_cyclic_count p hpodd
      _ = cyc S := cyc_eq_of_mulEquiv e
      _ ≤ cyc G := cyc_le_of_injective S.subtype S.subtype_injective
  simpa only [numPrimeFactors, Nat.card_eq_fintype_card] using hb

/-- Normal PSL2(p²) with trivial centralizer reaches the exact FC threshold,
using its actual automorphism-group order to derive an index dividing four. -/
theorem threshold_le_of_normal_square_psl2_trivial_centralizer
    {G : Type*} [Group G] [Fintype G]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (S : Subgroup G) [S.Normal]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2) ≃* S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  have hd := Conjecture55SquareFieldAut.normal_square_psl2_index_dvd_four S hC p hpodd e
  have hd' : S.index ∣ 2 ^ 2 := by simpa using hd
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
  exact fc_threshold_le_of_square_psl2_subgroup_index_pow_two p hpodd S e k hk

/-- The characteristic prime-power in an actual PSL2 embedding lies in the
odd part, so the extension degree is bounded by its factorization exponent. -/
theorem degree_le_factorization_of_psl2_embedding
    {G : Type*} [Group G] [Finite G]
    (p f a m : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f) (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m)
    (i : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f) →* G)
    (hi : Function.Injective i) : f ≤ m.factorization p := by
  have hoddSq : Odd ((p ^ f) ^ 2) := hpodd.pow.pow
  have htwo : 2 ∣ (p ^ f) ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hoddSq
    omega
  have hs : 2 * Nat.card
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) =
      p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [Conjecture55FieldTransport.card_psl2_galoisField p f hpodd hf]
    exact Nat.mul_div_cancel' (dvd_mul_of_dvd_right htwo _)
  have hd := Subgroup.card_dvd_of_injective i hi
  rw [hG] at hd
  have hpm := PrimePower.prime_power_dvd_odd_part p f a m _ hpodd hs hd
  exact ((Fact.out : p.Prime).pow_dvd_iff_le_factorization hm.pos.ne').mp hpm

/-- With every odd-prime exponent at most two, a normal actual Galois-field
PSL2 subgroup with trivial centralizer always gives the FC lower bound.
This includes all a=2,...,5 cases produced by the Sylow exponent route. -/
theorem threshold_le_of_normal_galoisField_psl2_factorization_le_two
    {G : Type*} [Group G] [Fintype G]
    (p f a m : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hf : 1 ≤ f) (hpq : 5 ≤ p ^ f) (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m) (hfac : ∀ r, m.factorization r ≤ 2)
    (S : Subgroup G) [S.Normal]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f) ≃* S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  have hf2 : f ≤ 2 :=
    (degree_le_factorization_of_psl2_embedding p f a m hpodd hf hm hG
      (S.subtype.comp e.toMonoidHom) (S.subtype_injective.comp e.injective)).trans (hfac p)
  have hcases : f = 1 ∨ f = 2 := by omega
  rcases hcases with rfl | rfl
  · have hp5 : 5 ≤ p := by simpa using hpq
    exact threshold_le_of_normal_psl2_trivial_centralizer hp5 S
      ((Conjecture55FieldTransport.psl2_galoisField_one_equiv p).symm.trans e) hC
  · exact threshold_le_of_normal_square_psl2_trivial_centralizer p hpodd S e hC

end
end Conjecture55DegreeAtMostTwo

#print axioms Conjecture55DegreeAtMostTwo.two_dvd_card_psl2_square
#print axioms Conjecture55DegreeAtMostTwo.fc_threshold_le_of_square_psl2_subgroup_index_pow_two
#print axioms Conjecture55DegreeAtMostTwo.threshold_le_of_normal_square_psl2_trivial_centralizer
#print axioms Conjecture55DegreeAtMostTwo.degree_le_factorization_of_psl2_embedding
#print axioms Conjecture55DegreeAtMostTwo.threshold_le_of_normal_galoisField_psl2_factorization_le_two
