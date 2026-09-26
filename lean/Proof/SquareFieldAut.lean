import Conjecture55Aut.PGammaL2
import Conjecture55Aut.PSL2Cardinality
import OuterIndexCore
import Mathlib.FieldTheory.Finite.GaloisField

noncomputable section
namespace Conjecture55SquareFieldAut
open Conjecture55Aut

def ringAutEquivZModAlgAut (p f : ℕ) [Fact p.Prime] :
    (GaloisField p f ≃+* GaloisField p f) ≃
      (GaloisField p f ≃ₐ[ZMod p] GaloisField p f) where
  toFun e := AlgEquiv.ofRingEquiv (fun a =>
    DFunLike.congr_fun (Subsingleton.elim
      (e.toRingHom.comp (algebraMap (ZMod p) (GaloisField p f)))
      (algebraMap (ZMod p) (GaloisField p f))) a)
  invFun e := e.toRingEquiv
  left_inv e := by ext; rfl
  right_inv e := by ext; rfl

theorem card_ringAut_galoisField (p f : ℕ) [Fact p.Prime] (hf : f ≠ 0) :
    Nat.card (GaloisField p f ≃+* GaloisField p f) = f := by
  rw [Nat.card_congr (ringAutEquivZModAlgAut p f), IsGalois.card_aut_eq_finrank,
    GaloisField.finrank p hf]

theorem card_mulAut_psl2_square (p : ℕ) [Fact p.Prime] (hpodd : Odd p) :
    Nat.card (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2))) =
      4 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2)) := by
  let K := GaloisField p 2
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    have hpne : p ≠ 2 := fun h => (by decide : ¬Odd (2 : ℕ)) (h ▸ hpodd)
    omega
  have hKcard : Nat.card K = p ^ 2 := GaloisField.card p 2 (by decide)
  have hK : IsOddPrimePower (Nat.card K) := ⟨p, 2, hp, hpodd, by decide, hKcard⟩
  have hcard : 3 < Nat.card K := by rw [hKcard]; nlinarith
  let f := pGammaL2ToMulAutPSL2 K hK hcard
  have hf : Function.Bijective f :=
    ⟨pGammaL2ToMulAutPSL2_injective K hK hcard,
      pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard⟩
  have heven : 2 ∣ p ^ 2 * ((p ^ 2) ^ 2 - 1) := by
    apply dvd_mul_of_dvd_right
    have hodd : Odd ((p ^ 2) ^ 2) := hpodd.pow.pow
    exact even_iff_two_dvd.mp (hodd.tsub_odd (by decide))
  change Nat.card (MulAut (PSL2 K)) = 4 * Nat.card (PSL2 K)
  calc
    Nat.card (MulAut (PSL2 K)) = Nat.card (PGammaL2 K) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card (PGL2 K) * 2 := by
      rw [PGammaL2, SemidirectProduct.card, card_ringAut_galoisField p 2 (by decide)]
    _ = (p ^ 2 * ((p ^ 2) ^ 2 - 1)) * 2 := by rw [pgl2_card_formula K, hKcard]
    _ = 4 * Nat.card (PSL2 K) := by
      rw [psl2_card_formula K hK, hKcard]
      have heq := Nat.mul_div_cancel' heven
      omega

theorem normal_square_psl2_index_dvd_four
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [S.Normal]
    (hC : Subgroup.centralizer (S : Set G) = ⊥)
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2) ≃* S) :
    S.index ∣ 4 := by
  apply Conjecture55OuterAut.normal_index_dvd_of_aut_card S hC 4
  rw [← Nat.card_congr (MulAut.congr e).toEquiv,
    card_mulAut_psl2_square p hpodd, Nat.card_congr e.toEquiv]

#print axioms ringAutEquivZModAlgAut
#print axioms card_ringAut_galoisField
#print axioms card_mulAut_psl2_square
#print axioms normal_square_psl2_index_dvd_four
end Conjecture55SquareFieldAut
