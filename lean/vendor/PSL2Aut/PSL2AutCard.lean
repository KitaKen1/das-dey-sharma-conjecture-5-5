import Conjecture55Aut.PGammaL2
import Conjecture55PSL2

namespace Conjecture55OuterAut

open Conjecture55Aut

lemma zmod_isOddPrimePower {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    IsOddPrimePower (Nat.card (ZMod p)) := by
  refine ⟨p, 1, Fact.out, ?_, by omega, by simp⟩
  have hodd : p % 2 = 1 :=
    (Nat.Prime.eq_two_or_odd (Fact.out : p.Prime)).resolve_left (by omega)
  exact ⟨p / 2, by omega⟩

/-- The automorphism group of PSL₂ over a prime field has twice the order
of PSL₂. This specializes the proved projective-semilinear automorphism theorem. -/
theorem card_mulAut_psl2 {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.card (MulAut (Conjecture55PSL2.PSL2 p)) =
      2 * Nat.card (Conjecture55PSL2.PSL2 p) := by
  have hK : IsOddPrimePower (Nat.card (ZMod p)) := zmod_isOddPrimePower hp
  have hcard : 3 < Nat.card (ZMod p) := by simpa using (show 3 < p by omega)
  let f := pGammaL2ToMulAutPSL2 (ZMod p) hK hcard
  have hf : Function.Bijective f :=
    ⟨pGammaL2ToMulAutPSL2_injective (ZMod p) hK hcard,
      pGammaL2ToMulAutPSL2_surjective (ZMod p) (p := p) (f := 1) (by simp) hK hcard⟩
  have hfield : Nat.card (ZMod p ≃+* ZMod p) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  calc
    Nat.card (MulAut (Conjecture55PSL2.PSL2 p)) = Nat.card (PGammaL2 (ZMod p)) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card (PGL2 (ZMod p)) := by
      rw [PGammaL2, SemidirectProduct.card, hfield, mul_one]
    _ = p * (p ^ 2 - 1) := by
      simpa only [Nat.card_zmod] using pgl2_card_formula (ZMod p)
    _ = 2 * Nat.card (Conjecture55PSL2.PSL2 p) := by
      simpa only [Nat.mul_comm] using (Conjecture55PSL2.card_psl2_mul_two hp).symm

#print axioms card_mulAut_psl2
#print axioms Conjecture55Aut.pGammaL2ToMulAutPSL2_surjective
#print axioms Conjecture55Aut.pGammaL2ToMulAutPSL2_injective

end Conjecture55OuterAut
