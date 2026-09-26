import Conjecture55Foundation
import Conjecture55Aut.PSL2Cardinality
import Conjecture55Aut.LinearRingEquiv
import PSL2CyclicCount
import Mathlib.FieldTheory.Finite.GaloisField

/-! From the actual Galois-field PSL₂ subgroup to the prime-field case. -/
namespace Conjecture55FieldTransport

/-- The actual order of PSL₂ over the Galois field of odd prime-power order. -/
theorem card_psl2_galoisField (p f : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hf : 1 ≤ f) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) =
      p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
  have hcard := GaloisField.card p f (by omega)
  have hodd : Conjecture55Aut.IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, hpodd, hf, hcard⟩
  simpa [hcard] using Conjecture55Aut.psl2_card_formula (GaloisField p f) hodd

/-- The coefficient-field equivalence at degree one induces the required
actual projective special linear group equivalence. -/
noncomputable def psl2_galoisField_one_equiv (p : ℕ) [Fact p.Prime] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1) ≃*
      Conjecture55PSL2.PSL2 p :=
  Conjecture55Aut.psl2RingEquiv (GaloisField.equivZmodP p).toRingEquiv

/-- An embedded actual Galois-field PSL₂ group in either allowed ambient
order shape must have field degree one. The order formula is derived. -/
theorem degree_eq_one_of_psl2_embedding_small_shape
    {G : Type*} [Group G] [Finite G]
    (p f a m : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f) (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m)
    (hshape : (a = 2 ∧ ∀ r, m.factorization r ≤ 2) ∨ (a = 3 ∧ Squarefree m))
    (i : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f) →* G)
    (hi : Function.Injective i) : f = 1 := by
  apply Conjecture55Lean4Web.PrimePower.exponent_eq_one_of_psl2_order_dvd_small_shape
    p f a m Fact.out hpodd hf hm ?_ hshape
  have hdvd := Subgroup.card_dvd_of_injective i hi
  rwa [card_psl2_galoisField p f hpodd hf, hG] at hdvd

/-- The small-order reduction yields both degree one and an explicit
prime-field PSL₂ model for the embedded Galois-field group. -/
theorem degree_eq_one_and_prime_field_equiv_of_embedding_small_shape
    {G : Type*} [Group G] [Finite G]
    (p f a m : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f) (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m)
    (hshape : (a = 2 ∧ ∀ r, m.factorization r ≤ 2) ∨ (a = 3 ∧ Squarefree m))
    (i : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f) →* G)
    (hi : Function.Injective i) :
    f = 1 ∧ Nonempty
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f) ≃*
        Conjecture55PSL2.PSL2 p) := by
  have hf1 := degree_eq_one_of_psl2_embedding_small_shape p f a m hpodd hf hm hG hshape i hi
  refine ⟨hf1, ?_⟩
  subst f
  exact ⟨psl2_galoisField_one_equiv p⟩

/-- The form used after classification: a subgroup presented over a Galois
field is equivalent to the existing prime-field PSL₂ model. -/
theorem degree_eq_one_and_prime_field_equiv_of_subgroup_small_shape
    {G : Type*} [Group G] [Finite G]
    (p f a m : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f) (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m)
    (hshape : (a = 2 ∧ ∀ r, m.factorization r ≤ 2) ∨ (a = 3 ∧ Squarefree m))
    (S : Subgroup G)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f) ≃* S) :
    f = 1 ∧ Nonempty (Conjecture55PSL2.PSL2 p ≃* S) := by
  have hf1 := degree_eq_one_of_psl2_embedding_small_shape p f a m hpodd hf hm hG hshape
    (S.subtype.comp e.toMonoidHom) (S.subtype_injective.comp e.injective)
  refine ⟨hf1, ?_⟩
  subst f
  exact ⟨(psl2_galoisField_one_equiv p).symm.trans e⟩

#print axioms card_psl2_galoisField
#print axioms psl2_galoisField_one_equiv
#print axioms degree_eq_one_of_psl2_embedding_small_shape
#print axioms degree_eq_one_and_prime_field_equiv_of_embedding_small_shape
#print axioms degree_eq_one_and_prime_field_equiv_of_subgroup_small_shape
end Conjecture55FieldTransport
