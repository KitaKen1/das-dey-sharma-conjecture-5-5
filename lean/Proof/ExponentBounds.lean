import ElementaryRoots
import FrobeniusBridge
import RootShape

/-! Sylow exponent bounds give a direct, quantitative cyclic-subgroup lower
bound. Ordinary root lower bounds remain explicit; no comparison bijection or
exact-root subgroup theorem is used. -/

open scoped BigOperators

namespace RootWeights
universe u
noncomputable section

/-- A bound for the exponent of one Sylow subgroup holds for every p-element. -/
theorem pow_eq_one_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s a : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (x : G) (hx : x ^ (p ^ a) = 1) : x ^ (p ^ s) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp
    (orderOf_dvd_of_pow_eq_one hx)
  have hX : IsPGroup p (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hk]
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  let y : Q := ⟨x, hQ (Subgroup.mem_zpowers x)⟩
  let e : Q ≃* P := Q.equiv P
  have hy : y ^ (p ^ s) = 1 := by
    apply e.injective
    simpa using hP (e y)
  exact congrArg (fun z : Q => (z : G)) hy

/-- Above the Sylow exponent, the p-part of a root exponent can be lowered.
No root-count divisibility theorem is used. -/
theorem roots_eq_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s j a d : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (hsj : s ≤ j) (hja : j ≤ a) :
    {x : G | x ^ (p ^ j * d) = 1} = {x : G | x ^ (p ^ a * d) = 1} := by
  ext x
  constructor
  · intro hx
    exact orderOf_dvd_of_pow_eq_one hx |>.trans
      (Nat.mul_dvd_mul_right (pow_dvd_pow p hja) d) |>
      orderOf_dvd_iff_pow_eq_one.mp
  · intro hx
    have hxd : (x ^ d) ^ (p ^ a) = 1 := by
      simpa [pow_mul, mul_comm] using hx
    have hs := pow_eq_one_of_sylow_exponent_bound hp P hP (x ^ d) hxd
    have hj : (x ^ d) ^ (p ^ j) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_pow_eq_one hs).trans (pow_dvd_pow p hsj))
    simpa [pow_mul, mul_comm] using hj

theorem card_roots_eq_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s j a d : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (hsj : s ≤ j) (hja : j ≤ a) :
    Nat.card {x : G // x ^ (p ^ j * d) = 1} =
      Nat.card {x : G // x ^ (p ^ a * d) = 1} := by
  have he := roots_eq_of_sylow_exponent_bound (d := d) hp P hP hsj hja
  exact Nat.card_congr (Equiv.setCongr he)

theorem root_lower_bound_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s j a m d : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (hcard : Nat.card G = p ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hd : d ∣ m) (hsj : s ≤ j) (hja : j ≤ a) :
    p ^ a * d ≤ Nat.card {x : G // x ^ (p ^ j * d) = 1} := by
  rw [card_roots_eq_of_sylow_exponent_bound hp P hP hsj hja]
  apply hbase
  rw [hcard]
  exact Nat.mul_dvd_mul_left _ hd

theorem orderOf_dvd_of_sylow_exponent_bound
    {G : Type*} [Group G] [Finite G] {p s a m : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : ∀ x : P, x ^ (p ^ s) = 1)
    (hcard : Nat.card G = p ^ a * m) (hsa : s ≤ a) (x : G) :
    orderOf x ∣ p ^ s * m := by
  have hx : x ^ (p ^ a * m) = 1 := by
    rw [← hcard]
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard x)
  have he := roots_eq_of_sylow_exponent_bound (d := m) hp P hP le_rfl hsa
  have hx' : x ∈ {x : G | x ^ (p ^ a * m) = 1} := hx
  rw [← he] at hx'
  exact orderOf_dvd_of_pow_eq_one hx'

/-- Nonnegative weighted root averages also compare formal linear combinations
of cyclic counts. The finite groups themselves need not be in bijection. -/
theorem cyclic_count_linear_comparison
    {G H K : Type*} [Group G] [Group H] [Group K]
    [Fintype G] [Fintype H] [Fintype K] {n : ℕ} [NeZero n] (c : ℕ)
    (hG : ∀ x : G, orderOf x ∣ n) (hH : ∀ x : H, orderOf x ∣ n)
    (hK : ∀ x : K, orderOf x ∣ n)
    (hroot : ∀ d ∈ n.divisors,
      (c + 1) * Nat.card {x : H // x ^ d = 1} ≤
        Nat.card {x : G // x ^ d = 1} + c * Nat.card {x : K // x ^ d = 1}) :
    (c + 1) * Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups H) ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) +
        c * Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups K) := by
  have hsum : (∑ u : (ZMod n)ˣ, ((c : ℚ) + 1) *
        (Nat.card {x : H // x ^ rootDivisor n u = 1} : ℚ)) ≤
      ∑ u : (ZMod n)ˣ, ((Nat.card {x : G // x ^ rootDivisor n u = 1} : ℚ) +
        c * (Nat.card {x : K // x ^ rootDivisor n u = 1} : ℚ)) := by
    apply Finset.sum_le_sum
    intro u _
    exact_mod_cast hroot _
      (Nat.mem_divisors.mpr ⟨rootDivisor_dvd n u, NeZero.ne n⟩)
  have hq := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n.totient : (0 : ℚ) ≤ _)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc,
    ← cyclic_count_eq_unit_average hG, ← cyclic_count_eq_unit_average hH,
    ← cyclic_count_eq_unit_average hK] at hq
  exact_mod_cast hq

theorem divisor_not_dvd_half_eq
    {s m e : ℕ} (hs : 1 ≤ s) (hm : Odd m)
    (he : e ∣ 2 ^ s * m) (hne : ¬ e ∣ 2 ^ (s - 1) * m) :
    ∃ d, d ∣ m ∧ e = 2 ^ s * d := by
  have hmpos := hm.pos
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he (by positivity)
  obtain ⟨j, d, hdOdd, heq⟩ := Nat.exists_eq_two_pow_mul_odd hepos.ne'
  have hj : j ≤ s := by
    apply (Nat.pow_dvd_pow_iff_le_right Nat.prime_two.one_lt).mp
    apply (hm.coprime_two_left.pow_left j).dvd_of_dvd_mul_right
    apply dvd_trans _ he
    rw [heq]
    exact dvd_mul_right _ _
  have hd : d ∣ m := by
    apply (hdOdd.coprime_two_right.pow_right s).dvd_of_dvd_mul_left
    apply dvd_trans _ he
    rw [heq]
    exact dvd_mul_left _ _
  have hjs : j = s := by
    by_contra h
    apply hne
    rw [heq]
    exact mul_dvd_mul (pow_dvd_pow 2 (by omega)) hd
  exact ⟨d, hd, by simpa [hjs] using heq⟩

theorem gcd_half_two_pow_mul
    {s m d : ℕ} (hs : 1 ≤ s) (hm : Odd m) (hd : d ∣ m) :
    Nat.gcd (2 ^ (s - 1) * m) (2 ^ s * d) = 2 ^ (s - 1) * d := by
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  rw [hpow, mul_assoc, Nat.gcd_mul_left]
  congr 1
  rw [Nat.gcd_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd hm.coprime_two_left hd

/-- Root estimates at the largest 2-power divisor yield a cyclic-count bound.
This uses a linear combination of two cyclic groups and positivity of the
unit-average weights, rather than a comparison bijection. -/
theorem cyclic_count_ge_of_top_root_bounds
    {G : Type*} [Group G] [Fintype G] {s m c : ℕ} (hs : 1 ≤ s) (hm : Odd m)
    (horder : ∀ x : G, orderOf x ∣ 2 ^ s * m)
    (hbase : ∀ e, e ∣ 2 ^ s * m → e ≤ Nat.card {x : G // x ^ e = 1})
    (htop : ∀ d, d ∣ m → (c + 2) * (2 ^ (s - 1) * d) ≤
      Nat.card {x : G // x ^ (2 ^ s * d) = 1}) :
    (s + c + 1) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hmpos := hm.pos
  let : NeZero (2 ^ s * m) := ⟨by positivity⟩
  let : NeZero (2 ^ (s - 1) * m) := ⟨by positivity⟩
  let H := Multiplicative (ZMod (2 ^ s * m))
  let K := Multiplicative (ZMod (2 ^ (s - 1) * m))
  have hH : Nat.card H = 2 ^ s * m := by simp [H]
  have hK : Nat.card K = 2 ^ (s - 1) * m := by simp [K]
  have hhalf : 2 ^ (s - 1) * m ∣ 2 ^ s * m :=
    Nat.mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) m
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  have hlinear := cyclic_count_linear_comparison (G := G) (H := H) (K := K)
    (n := 2 ^ s * m) c horder
    (fun x => by simpa only [hH] using orderOf_dvd_natCard x)
    (fun x => (show orderOf x ∣ 2 ^ (s - 1) * m from by
      simpa only [hK] using orderOf_dvd_natCard x).trans hhalf) (by
      intro e he
      have hed := (Nat.mem_divisors.mp he).1
      rw [card_roots_cyclic, card_roots_cyclic, hH, hK, Nat.gcd_eq_right hed]
      by_cases hehalf : e ∣ 2 ^ (s - 1) * m
      · rw [Nat.gcd_eq_right hehalf]
        have hb := hbase e hed
        nlinarith
      · obtain ⟨d, hd, rfl⟩ := divisor_not_dvd_half_eq hs hm hed hehalf
        rw [gcd_half_two_pow_mul hs hm hd]
        have ht := htop d hd
        rw [hpow] at ht ⊢
        nlinarith)
  have hcH : Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups H) =
      (s + 1) * m.divisors.card := by
    rw [Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_divisors_card, hH,
      (hm.coprime_two_left.pow_left s).card_divisors_mul,
      Nat.divisors_prime_pow Nat.prime_two]
    simp
  have hcK : Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups K) =
      s * m.divisors.card := by
    rw [Conjecture55Lean4Web.CyclicSum.cyclic_count_eq_divisors_card, hK,
      (hm.coprime_two_left.pow_left (s - 1)).card_divisors_mul,
      Nat.divisors_prime_pow Nat.prime_two]
    simp [Nat.sub_add_cancel hs]
  rw [hcH, hcK] at hlinear
  nlinarith

/-- Proposition E: ordinary root lower bounds and a bound on the Sylow
2-exponent imply the precise lower bound `(s-1+2^(a-s+1)) τ(m)`.
The ordinary root lower bound is explicitly assumed. -/
theorem cyclic_count_ge_of_sylow_exponent_bound
    {G : Type*} [Group G] [Fintype G] {s a m : ℕ}
    (hs : 1 ≤ s) (hsa : s ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hP : ∀ x : P, x ^ (2 ^ s) = 1)
    (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1}) :
    (s - 1 + 2 ^ (a - s + 1)) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hq : 2 ≤ 2 ^ (a - s + 1) := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
      (show 1 ≤ a - s + 1 by omega)
  have hpow : 2 ^ (a - s + 1) * 2 ^ (s - 1) = 2 ^ a := by
    rw [← pow_add]
    congr 1
    omega
  have hb := cyclic_count_ge_of_top_root_bounds (c := 2 ^ (a - s + 1) - 2) hs hm
    (orderOf_dvd_of_sylow_exponent_bound Nat.prime_two P hP hcard hsa)
    (fun e he => hbase e (he.trans (by
      rw [hcard]
      exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 hsa) m))) (by
      intro d hd
      rw [Nat.sub_add_cancel hq, ← mul_assoc, hpow]
      exact root_lower_bound_of_sylow_exponent_bound Nat.prime_two P hP
        hcard hbase hd le_rfl hsa)
  convert hb using 1
  congr 1
  omega

theorem sylow_card_eq_two_part
    {G : Type*} [Group G] [Finite G] {a m : ℕ} (P : Sylow 2 G)
    (hm : Odd m) (hcard : Nat.card G = 2 ^ a * m) : Nat.card P = 2 ^ a := by
  rw [P.card_eq_multiplicity, hcard,
    Nat.factorization_mul (by positivity) hm.pos.ne']
  simp [Nat.prime_two.factorization_pow,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat]

/-- Noncyclic Sylow subgroups give `(a+2) τ(m)` using ordinary root bounds. -/
theorem cyclic_count_ge_of_noncyclic_sylow
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1}) :
    (a + 2) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  have hPc : Nat.card P = 2 ^ ((a - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact sylow_card_eq_two_part P hm hcard
  have hP := AmiriNext.pow_eq_one_of_prime_power_card_not_cyclic
    Nat.prime_two hPc hnc
  have h := cyclic_count_ge_of_sylow_exponent_bound (s := a - 1)
    (by omega) (by omega) hm P hP hcard hbase
  have he : a - (a - 1) + 1 = 2 := by omega
  simpa only [he, show (2 : ℕ) ^ 2 = 4 by norm_num,
    show a - 1 - 1 + 4 = a + 2 by omega] using h

/-- Under the actual strict FC threshold, an ordinary Frobenius lower bound
already forces the 2-part exponent to be at most five. -/
theorem two_part_le_five_of_noncyclic_sylow
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : Conjecture55Lean4Web.cyc G <
      2 ^ (Conjecture55Lean4Web.numPrimeFactors G + 2)) : a ≤ 5 := by
  by_contra h
  have hcount := cyclic_count_ge_of_noncyclic_sylow ha hm P hnc hcard hbase
  have hcount8 : 8 * m.divisors.card ≤ Conjecture55Lean4Web.cyc G :=
    (Nat.mul_le_mul_right _ (by omega : 8 ≤ a + 2)).trans hcount
  exact Nat.not_lt_of_ge
    (Conjecture55RootShape.threshold_le_of_eight_mul_divisor_count
      a m (by omega) hm hcard hcount8) hlt

/-- A second exponent drop is impossible below the FC threshold. This gives
an actual element generating a cyclic subgroup of index two in the Sylow group. -/
theorem exists_order_half_sylow_card_of_strict_fc_bound
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 3 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : Conjecture55Lean4Web.cyc G <
      2 ^ (Conjecture55Lean4Web.numPrimeFactors G + 2)) :
    ∃ x : P, orderOf x = 2 ^ (a - 1) := by
  by_contra h
  push Not at h
  have hPc := sylow_card_eq_two_part P hm hcard
  have hP : ∀ x : P, x ^ (2 ^ (a - 2)) = 1 := by
    intro x
    have hd : orderOf x ∣ 2 ^ a := hPc ▸ orderOf_dvd_natCard x
    obtain ⟨k, hka, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hkne : k ≠ a := by
      intro hka'
      apply hnc
      exact isCyclic_of_orderOf_eq_card x (by rw [hk, hka', hPc])
    have hkne' : k ≠ a - 1 := by
      intro hka'
      exact h x (by rw [hk, hka'])
    exact orderOf_dvd_iff_pow_eq_one.mp (hk ▸ pow_dvd_pow 2 (by omega))
  have hcount := cyclic_count_ge_of_sylow_exponent_bound (s := a - 2)
    (by omega) (by omega) hm P hP hcard hbase
  have he : a - (a - 2) + 1 = 3 := by omega
  have hcount' : (a + 5) * m.divisors.card ≤ Conjecture55Lean4Web.cyc G := by
    change (a + 5) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G)
    simpa only [he, show (2 : ℕ) ^ 3 = 8 by norm_num,
      show a - 2 - 1 + 8 = a + 5 by omega] using hcount
  have hcount8 : 8 * m.divisors.card ≤ Conjecture55Lean4Web.cyc G :=
    (Nat.mul_le_mul_right _ (by omega : 8 ≤ a + 5)).trans hcount'
  exact Nat.not_lt_of_ge
    (Conjecture55RootShape.threshold_le_of_eight_mul_divisor_count
      a m (by omega) hm hcard hcount8) hlt

theorem exists_cyclic_index_two_of_strict_fc_bound
    {G : Type*} [Group G] [Fintype G] {a m : ℕ} (ha : 3 ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hnc : ¬ IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : Conjecture55Lean4Web.cyc G <
      2 ^ (Conjecture55Lean4Web.numPrimeFactors G + 2)) :
    ∃ C : Subgroup P, IsCyclic C ∧ C.index = 2 := by
  obtain ⟨x, hx⟩ := exists_order_half_sylow_card_of_strict_fc_bound
    ha hm P hnc hcard hbase hlt
  refine ⟨Subgroup.zpowers x, inferInstance, ?_⟩
  have hc := (Subgroup.zpowers x).card_mul_index
  rw [Nat.card_zpowers, hx] at hc
  have hPc : Nat.card P = 2 ^ a := sylow_card_eq_two_part P hm hcard
  have hc' : 2 ^ (a - 1) * (Subgroup.zpowers x).index = 2 ^ a := hc.trans hPc
  have hpow : 2 ^ a = 2 ^ (a - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hpow] at hc'
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (a - 1)) hc'

/-- The only external mathematical input to Proposition E can be supplied by
ordinary Frobenius divisibility; no exact-root subgroup input is present. -/
theorem cyclic_count_ge_of_frobenius_and_sylow_exponent
    (hdiv : Conjecture55Frobenius.RootDivisibilityInput.{u})
    {G : Type u} [Group G] [Fintype G] {s a m : ℕ}
    (hs : 1 ≤ s) (hsa : s ≤ a) (hm : Odd m)
    (P : Sylow 2 G) (hP : ∀ x : P, x ^ (2 ^ s) = 1)
    (hcard : Nat.card G = 2 ^ a * m) :
    (s - 1 + 2 ^ (a - s + 1)) * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) :=
  cyclic_count_ge_of_sylow_exponent_bound hs hsa hm P hP hcard
    (fun e he => Conjecture55Frobenius.root_lower_bound_of_divisibility hdiv e he)

end
end RootWeights

#print axioms RootWeights.pow_eq_one_of_sylow_exponent_bound
#print axioms RootWeights.roots_eq_of_sylow_exponent_bound
#print axioms RootWeights.card_roots_eq_of_sylow_exponent_bound
#print axioms RootWeights.root_lower_bound_of_sylow_exponent_bound
#print axioms RootWeights.orderOf_dvd_of_sylow_exponent_bound
#print axioms RootWeights.cyclic_count_linear_comparison
#print axioms RootWeights.divisor_not_dvd_half_eq
#print axioms RootWeights.gcd_half_two_pow_mul
#print axioms RootWeights.cyclic_count_ge_of_top_root_bounds
#print axioms RootWeights.cyclic_count_ge_of_sylow_exponent_bound
#print axioms RootWeights.sylow_card_eq_two_part
#print axioms RootWeights.cyclic_count_ge_of_noncyclic_sylow
#print axioms RootWeights.two_part_le_five_of_noncyclic_sylow
#print axioms RootWeights.exists_order_half_sylow_card_of_strict_fc_bound
#print axioms RootWeights.exists_cyclic_index_two_of_strict_fc_bound
#print axioms RootWeights.cyclic_count_ge_of_frobenius_and_sylow_exponent
