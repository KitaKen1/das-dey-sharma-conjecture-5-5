import TwoTori
import SquareFieldArithmetic

/-! The actual PSL2 over GF(p²) satisfies the FC cyclic-subgroup threshold
for every odd prime p, including p=3. No classification or root-count
divisibility input is assumed. -/

namespace Conjecture55SquareField

theorem psl2_square_fc_threshold_lt_cyclic_count
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) :
    2 ^ ((Nat.card
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2))).primeFactors.card + 2) <
      Nat.card (CyclicSum.CyclicSubgroups
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2))) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    have hod := Nat.odd_iff.mp hpodd
    omega
  have hq : 5 ≤ p ^ 2 := by nlinarith
  calc
    _ < (p ^ 2) ^ 2 := by
      rw [Conjecture55FieldTransport.card_psl2_galoisField p 2 hpodd (by omega)]
      exact psl2_square_primeFactor_threshold_lt p hp hpodd
    _ ≤ _ := psl2_galoisField_cyclic_count_ge_square p 2 hpodd (by omega) hq

theorem psl2_square_fc_threshold_le_cyclic_count
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) :
    2 ^ ((Nat.card
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2))).primeFactors.card + 2) ≤
      Nat.card (CyclicSum.CyclicSubgroups
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2))) :=
  (psl2_square_fc_threshold_lt_cyclic_count p hpodd).le

end Conjecture55SquareField

#print axioms Conjecture55SquareField.psl2_square_fc_threshold_lt_cyclic_count
#print axioms Conjecture55SquareField.psl2_square_fc_threshold_le_cyclic_count
