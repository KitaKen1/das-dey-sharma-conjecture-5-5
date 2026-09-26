import RootDescent
import ElementaryRoots

/-! The full exact-root theorem can be restricted to odd exponents.
The restricted theorem and ordinary Frobenius remain explicit inputs. -/
namespace Conjecture55OddRootBypass
open Conjecture55Frobenius Conjecture55AmiriBypass
universe u

def OddExactRootSubgroupInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], ∀ d : ℕ, Odd d → d ∣ Nat.card G →
    Nat.card {x : G // x ^ d = 1} = d →
      ∃ N : Subgroup G, Nat.card N = d ∧ ∀ x : G, x ^ d = 1 → x ∈ N

theorem normal_of_card_eq_and_contains_roots
    {G : Type u} [Group G] [Finite G] (d : ℕ)
    (N : Subgroup G) (hN : Nat.card N = d)
    (hroots : ∀ x : G, x ^ d = 1 → x ∈ N) : N.Normal := by
  constructor
  intro x hx g
  apply hroots
  have hxN : (⟨x, hx⟩ : N) ^ d = 1 := by
    rw [← hN]
    exact pow_card_eq_one'
  have hxpow : x ^ d = 1 := congrArg Subtype.val hxN
  change (MulAut.conj g x) ^ d = 1
  rw [← map_pow, hxpow, map_one]

theorem odd_exact_root_count_eq_one
    (hexact : OddExactRootSubgroupInput.{u})
    {G : Type u} [Group G] [Finite G]
    (hnoOdd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (d : ℕ) (hdodd : Odd d) (hd : d ∣ Nat.card G)
    (heq : Nat.card {x : G // x ^ d = 1} = d) : d = 1 := by
  obtain ⟨N, hN, hroots⟩ := hexact G d hdodd hd heq
  have hnormal := normal_of_card_eq_and_contains_roots d N hN hroots
  have hbot := hnoOdd N hnormal (hN.symm ▸ hdodd)
  simpa [hbot] using hN.symm

theorem double_root_bound_of_odd_exact
    (hdiv : RootDivisibilityInput.{u}) (hexact : OddExactRootSubgroupInput.{u})
    {G : Type u} [Group G] [Finite G]
    (hnoOdd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (E : Subgroup G) (hE : Nat.card E = 4) (hEpow : ∀ x : E, x ^ 2 = 1)
    (j d : ℕ) (hj : 1 ≤ j) (hdodd : Odd d)
    (hbig : 2 ^ (j + 1) * d ∣ Nat.card G) :
    2 ^ (j + 1) * d ≤ Nat.card {x : G // x ^ (2 ^ j * d) = 1} := by
  have hsmall : 2 ^ j * d ∣ Nat.card G :=
    (mul_dvd_mul (pow_dvd_pow 2 (by omega : j ≤ j + 1)) (dvd_refl d)).trans hbig
  have hn : 0 < 2 ^ j * d := Nat.pos_of_dvd_of_pos hsmall Nat.card_pos
  have hlo := root_lower_bound_of_divisibility hdiv (G := G) (2 ^ j * d) hsmall
  obtain ⟨k, hk⟩ := hdiv G (2 ^ j * d) hsmall
  by_contra hbound
  have hlt : Nat.card {x : G // x ^ (2 ^ j * d) = 1} < 2 * (2 ^ j * d) := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using Nat.lt_of_not_ge hbound
  have hk1 : k = 1 := by nlinarith
  have heq : Nat.card {x : G // x ^ (2 ^ j * d) = 1} = 2 ^ j * d := by
    simpa [hk1] using hk
  have hdesc := exact_root_count_descends_two_part hdiv j d hbig heq
  have hd : d ∣ Nat.card G := (dvd_mul_left d (2 ^ (j + 1))).trans hbig
  have hd1 := odd_exact_root_count_eq_one hexact hnoOdd d hdodd hd hdesc
  subst d
  simp only [mul_one] at hbig heq
  have hnc : ¬IsCyclic E := by
    intro h
    let : IsCyclic E := h
    have hc : Nat.card E ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hEpow
    norm_num [hE] at hc
  have hb := AmiriNext.prime_power_le_card_roots_of_noncyclic_subgroup
    (j := j) (d := 1) Nat.prime_two E (by simpa using hE : Nat.card E = 2 ^ 2)
    hnc (by omega) hbig
  simp only [mul_one, heq] at hb
  have hp : 0 < 2 ^ j := by positivity
  rw [pow_succ] at hb
  omega

theorem no_odd_normal_of_radicalFree
    {G : Type u} [Group G] [Finite G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hodd : ∀ (H : Type u) [Group H] [Finite H], Odd (Nat.card H) → Group.IsSolvable H) :
    ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  intro N hn ho
  exact hrad N hn (hodd N ho)

theorem cyclic_count_lower_bound_of_odd_exact
    (hdiv : RootDivisibilityInput.{u}) (hexact : OddExactRootSubgroupInput.{u})
    {G : Type u} [Group G] [Fintype G]
    (hnoOdd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (a m : ℕ) (ha : 2 ≤ a) (hm : Odd m) (hcard : Nat.card G = 2 ^ a * m)
    (E : Subgroup G) (hE : Nat.card E = 4) (hEpow : ∀ x : E, x ^ 2 = 1) :
    2 * a * m.divisors.card ≤
      Nat.card (Conjecture55Lean4Web.CyclicSum.CyclicSubgroups G) := by
  apply RootWeights.cyclic_count_ge_two_mul_exponent_mul_divisors (by omega) hm hcard
  · exact fun n hn => root_lower_bound_of_divisibility hdiv n hn
  · intro d hd j hj hja
    apply double_root_bound_of_odd_exact hdiv hexact hnoOdd E hE hEpow j d hj
      (hm.of_dvd_nat hd)
    rw [hcard]
    exact mul_dvd_mul (pow_dvd_pow 2 (by omega : j + 1 ≤ a)) hd

#print axioms normal_of_card_eq_and_contains_roots
#print axioms odd_exact_root_count_eq_one
#print axioms double_root_bound_of_odd_exact
#print axioms no_odd_normal_of_radicalFree
#print axioms cyclic_count_lower_bound_of_odd_exact
end Conjecture55OddRootBypass
