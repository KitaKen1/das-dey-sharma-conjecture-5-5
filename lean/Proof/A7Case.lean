import A7Count
import AlternatingAutIndex
import PSL2Case

/-! The actual A7 count and automorphism theorem give the ambient FC bound. -/
namespace Conjecture55A7Count
open Conjecture55Lean4Web Conjecture55Lean4Web

theorem threshold_le_of_normal_a7_trivial_centralizer
    {G : Type*} [Group G] [Fintype G]
    (S : Subgroup G) [S.Normal] (e : alternatingGroup (Fin 7) ≃* S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  have hd := Conjecture55AlternatingAut.normal_a7_index_dvd_two S hC e
  have hd' : S.index ∣ 2 ^ 1 := by simpa using hd
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
  have hcard := Nat.card_congr e.toEquiv
  have h2 : 2 ∣ Nat.card S := by rw [← hcard, AlternatingSeven.card_a7]; norm_num
  have hprimes : (Nat.card G).primeFactors =
      (Nat.card (alternatingGroup (Fin 7))).primeFactors := by
    rw [PSL2Extensions.primeFactors_eq_of_index_pow_two S h2 k hk, hcard]
  have hb : 2 ^ ((Nat.card G).primeFactors.card + 2) ≤ cyc G := by
    rw [hprimes]
    calc
      _ ≤ cyc (alternatingGroup (Fin 7)) := by
        simpa only [numPrimeFactors, ← Nat.card_eq_fintype_card] using a7_fc_threshold_lt.le
      _ = cyc S := cyc_eq_of_mulEquiv e
      _ ≤ cyc G := cyc_le_of_injective S.subtype S.subtype_injective
  simpa only [numPrimeFactors, Nat.card_eq_fintype_card] using hb

#print axioms threshold_le_of_normal_a7_trivial_centralizer
end Conjecture55A7Count
