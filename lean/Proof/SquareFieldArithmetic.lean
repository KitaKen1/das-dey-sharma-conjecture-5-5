import Conjecture55Foundation

/-! For an odd prime p, the PSL2(p²) numerical order has an FC threshold
strictly below p⁴. Only elementary prime-factor arithmetic is used. -/

open scoped BigOperators

namespace Conjecture55SquareField

theorem two_pow_card_primeFactors_le (n : ℕ) (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n := by
  calc
    2 ^ n.primeFactors.card ≤ ∏ x ∈ n.primeFactors, x := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun _ _ => by omega)
      intro x hx
      exact (Nat.mem_primeFactors.mp hx).1.two_le
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

theorem psl2_square_primeFactor_threshold_lt (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    2 ^ (((p ^ 2 * ((p ^ 2) ^ 2 - 1) / 2)).primeFactors.card + 2) < (p ^ 2) ^ 2 := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    have hod := Nat.odd_iff.mp hpodd
    omega
  have hmod := Conjecture55Lean4Web.PrimePower.odd_fourth_mod_sixteen p hpodd
  have h16 : 16 ∣ (p ^ 2) ^ 2 - 1 := by
    rw [← pow_mul]
    norm_num only [Nat.reduceMul]
    omega
  obtain ⟨k, hk⟩ := h16
  have hpSq : 1 ≤ (p ^ 2) ^ 2 := by
    have hpos : 0 < (p ^ 2) ^ 2 := by positivity
    omega
  have hp9 : 9 ≤ p ^ 2 := by nlinarith
  have hkpos : 0 < k := by nlinarith [Nat.sub_add_cancel hpSq]
  have horder : p ^ 2 * ((p ^ 2) ^ 2 - 1) / 2 = p ^ 2 * (8 * k) := by
    rw [hk, show p ^ 2 * (16 * k) = (p ^ 2 * (8 * k)) * 2 by ring]
    simp
  have hpf : (8 * k).primeFactors = (2 * k).primeFactors := by
    rw [Nat.primeFactors_mul (by norm_num) hkpos.ne',
      Nat.primeFactors_mul (by norm_num) hkpos.ne',
      show (8 : ℕ) = 2 ^ 3 by norm_num,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.prime_two.primeFactors]
  have hcard : (p ^ 2 * ((p ^ 2) ^ 2 - 1) / 2).primeFactors.card ≤
      (2 * k).primeFactors.card + 1 := by
    rw [horder, Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (by positivity),
      Nat.primeFactors_prime_pow (by norm_num) hp, hpf]
    simpa using Finset.card_insert_le p (2 * k).primeFactors
  have hpow : 2 ^ ((p ^ 2 * ((p ^ 2) ^ 2 - 1) / 2).primeFactors.card + 2) ≤
      8 * 2 ^ (2 * k).primeFactors.card := by
    calc
      _ ≤ 2 ^ ((2 * k).primeFactors.card + 3) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ = _ := by rw [pow_add]; ring
  have hbase := two_pow_card_primeFactors_le (2 * k) (by positivity)
  nlinarith [Nat.sub_add_cancel hpSq]

end Conjecture55SquareField

#print axioms Conjecture55SquareField.two_pow_card_primeFactors_le
#print axioms Conjecture55SquareField.psl2_square_primeFactor_threshold_lt
