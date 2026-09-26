import FieldTransport
import AlmostSimpleCase

/-! The actual odd-prime-power PSL₂ almost-simple case of the FC threshold. -/

namespace Conjecture55PrimePowerCase
open Conjecture55Lean4Web

/-- A normal Galois-field PSL₂ subgroup with trivial ambient centralizer
meets the exact FC threshold under the allowed ambient order shape.
The field degree, prime-field equivalence, subgroup index, and automorphism
cardinality are all derived, rather than supplied as additional hypotheses. -/
theorem threshold_le_of_normal_galoisField_psl2_trivial_centralizer
    {G : Type*} [Group G] [Fintype G]
    (p f a m : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hf : 1 ≤ f) (hpq : 5 ≤ p ^ f) (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m)
    (hshape : (a = 2 ∧ ∀ r, m.factorization r ≤ 2) ∨ (a = 3 ∧ Squarefree m))
    (S : Subgroup G) [S.Normal]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f) ≃* S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  obtain ⟨hf1, ⟨eprime⟩⟩ :=
    Conjecture55FieldTransport.degree_eq_one_and_prime_field_equiv_of_subgroup_small_shape
      p f a m hpodd hf hm hG hshape S e
  have hp5 : 5 ≤ p := by simpa [hf1] using hpq
  exact Conjecture55Lean4Web.threshold_le_of_normal_psl2_trivial_centralizer hp5 S eprime hC

#print axioms threshold_le_of_normal_galoisField_psl2_trivial_centralizer
end Conjecture55PrimePowerCase
