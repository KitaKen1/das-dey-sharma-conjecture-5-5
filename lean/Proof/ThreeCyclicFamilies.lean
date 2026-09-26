import ConjugateOddFamilies
import SimpleNormalizerIndex
import OddSquarefreeArithmetic

/-! A classification-free counting bound from normalized cyclic subgroups
of orders two, four, and eight inside a nonabelian simple subgroup. -/

open scoped BigOperators
namespace Conjecture55ThreeFamilies
open Conjecture55PartialCount Conjecture55ConjugateOdd
open Conjecture55SimpleNormalizer Conjecture55OddSquarefree
open Conjecture55Lean4Web.CyclicSum
noncomputable section
variable {G : Type*} [Group G] [Finite G]

theorem factor_of_sylow_le {a m : ℕ} (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m) (P : Sylow 2 G)
    (N : Subgroup G) (hPN : (P : Subgroup G) ≤ N) :
    Odd N.index ∧ ∃ c, Odd c ∧ m = c * N.index ∧ Nat.card N = 2 ^ a * c := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd P.index := Nat.not_even_iff_odd.mp (by
    simpa only [even_iff_two_dvd] using P.not_dvd_index)
  have hnodd : Odd N.index := Odd.of_dvd_nat hpodd (Subgroup.index_dvd_of_le hPN)
  have hd : N.index ∣ m := by
    apply (hnodd.coprime_two_right.pow_right a).dvd_of_dvd_mul_left
    rw [← hG]
    exact N.index_dvd_card
  obtain ⟨c, hmc⟩ := hd
  have hfactor : m = c * N.index := hmc.trans (Nat.mul_comm _ _)
  have hc : Odd c := Odd.of_dvd_nat hm (by rw [hmc]; exact dvd_mul_left _ _)
  refine ⟨hnodd, c, hc, hfactor, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (m := N.index) hnodd.pos
  simpa only [hG, hfactor, mul_assoc] using N.card_mul_index

theorem five_tau_le_two_family {a m j : ℕ} (hm : Odd m) (hsf : Squarefree m)
    (hG : Nat.card G = 2 ^ a * m) (P : Sylow 2 G)
    (S A : Subgroup G) (hs : IsSimpleGroup S) (hn : ¬IsMulCommutative S)
    (h4 : 4 ∣ Nat.card S) [IsCyclic A] (hA : Nat.card A = 2 ^ (j + 1))
    (hAS : A ≤ S) (hPN : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G)) :
    5 * m.divisors.card ≤ 2 * Nat.card (CyclicWithTwoPart G j) := by
  obtain ⟨ho, c, hc, hmc, hNC⟩ := factor_of_sylow_le hm hG P
    (Subgroup.normalizer (A : Set G)) hPN
  have hAbot : A ≠ ⊥ := by
    intro he
    have hpos : 2 ≤ 2 ^ (j + 1) := by
      simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ j + 1)
    rw [he, Subgroup.card_bot] at hA
    omega
  have h5 := odd_normalizer_index_ge_five S A hs hn h4 hAbot hAS ho
  have harith := normalizer_gain hsf ho h5 hmc
  have hcount := normalizer_index_mul_divisors_le A hA hc (by
    rw [hNC]; exact dvd_mul_left _ _)
  omega

theorem two_exponents_eq {i j d e : ℕ} (hd : Odd d) (he : Odd e)
    (h : 2 ^ (i + 1) * d = 2 ^ (j + 1) * e) : i = j := by
  have factor (k t : ℕ) (ht : Odd t) :
      (2 ^ (k + 1) * t).factorization 2 = k + 1 := by
    rw [Nat.factorization_mul (by positivity) ht.pos.ne']
    simp [Nat.prime_two.factorization_pow,
      Nat.factorization_eq_zero_of_not_dvd ht.not_two_dvd_nat]
  have hf := congrArg (fun n : ℕ => n.factorization 2) h
  rw [factor _ _ hd, factor _ _ he] at hf
  omega

def forgetTwoPart : (Σ i : Fin 3, CyclicWithTwoPart G i.val) → CyclicSubgroups G :=
  fun x => x.2.1

theorem forgetTwoPart_injective : Function.Injective (forgetTwoPart (G := G)) := by
  rintro ⟨i, H⟩ ⟨j, K⟩ heq
  obtain ⟨d, hd, hHd⟩ := H.2
  obtain ⟨e, he, hKe⟩ := K.2
  have hc := congrArg (fun L : CyclicSubgroups G => Nat.card L.1) heq
  have hij : i = j := Fin.ext (two_exponents_eq hd he (hHd.symm.trans (hc.trans hKe)))
  subst j
  have hHK : H = K := Subtype.ext heq
  subst K
  rfl

theorem odd_ne_twoPart {m : ℕ} (hm : Odd m) (H : CyclicDividing G m)
    (x : Σ i : Fin 3, CyclicWithTwoPart G i.val) : H.1 ≠ forgetTwoPart x := by
  intro heq
  have ho : Odd (Nat.card H.1.1) := Odd.of_dvd_nat hm H.2
  obtain ⟨d, _, hcard⟩ := x.2.2
  have hEq := congrArg (fun L : CyclicSubgroups G => Nat.card L.1) heq
  have h2 : 2 ∣ Nat.card x.2.1.1 := by
    rw [hcard, pow_succ', mul_assoc]
    exact dvd_mul_right _ _
  exact ho.not_two_dvd_nat (hEq ▸ h2)

set_option maxHeartbeats 1000000 in
theorem cyclic_count_ge_odd_and_three_families {m : ℕ} (hm : Odd m) :
    Nat.card (CyclicDividing G m) +
      Nat.card (CyclicWithTwoPart G 0) + Nat.card (CyclicWithTwoPart G 1) +
      Nat.card (CyclicWithTwoPart G 2) ≤ Nat.card (CyclicSubgroups G) := by
  classical
  have hi : Function.Injective (Sum.elim
      (Subtype.val : CyclicDividing G m → CyclicSubgroups G) forgetTwoPart) :=
    Subtype.val_injective.sumElim forgetTwoPart_injective (odd_ne_twoPart hm)
  have h := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_sum, Nat.card_sigma] at h
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using h

/-- Three normalized cyclic subgroups, with the indicated exact orders,
give a bound strictly beyond the FC threshold when m is squarefree. -/
theorem seventeen_tau_le_two_cyclic_count {a m : ℕ} (hm : Odd m) (hsf : Squarefree m)
    (hG : Nat.card G = 2 ^ a * m) (P : Sylow 2 G)
    (S : Subgroup G) (hs : IsSimpleGroup S) (hn : ¬IsMulCommutative S)
    (h4 : 4 ∣ Nat.card S) (A : Fin 3 → Subgroup G)
    (hcyc : ∀ i, IsCyclic (A i)) (hcard : ∀ i, Nat.card (A i) = 2 ^ (i.val + 1))
    (hAS : ∀ i, A i ≤ S)
    (hPN : ∀ i, (P : Subgroup G) ≤ Subgroup.normalizer (A i : Set G)) :
    17 * m.divisors.card ≤ 2 * Nat.card (CyclicSubgroups G) := by
  classical
  let := Fintype.ofFinite G
  have hf (i : Fin 3) : 5 * m.divisors.card ≤
      2 * Nat.card (CyclicWithTwoPart G i.val) := by
    let : IsCyclic (A i) := hcyc i
    exact five_tau_le_two_family hm hsf hG P S (A i) hs hn h4
      (hcard i) (hAS i) (hPN i)
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  have hodd := divisors_card_le_cyclicDividing (G := G) (n := m) (by
    rw [hG]; exact dvd_mul_left _ _)
  have hsum := cyclic_count_ge_odd_and_three_families (G := G) hm
  change 5 * m.divisors.card ≤ 2 * Nat.card (CyclicWithTwoPart G 0) at h0
  change 5 * m.divisors.card ≤ 2 * Nat.card (CyclicWithTwoPart G 1) at h1
  change 5 * m.divisors.card ≤ 2 * Nat.card (CyclicWithTwoPart G 2) at h2
  omega

#print axioms five_tau_le_two_family
#print axioms forgetTwoPart_injective
#print axioms cyclic_count_ge_odd_and_three_families
#print axioms seventeen_tau_le_two_cyclic_count
end
end Conjecture55ThreeFamilies
