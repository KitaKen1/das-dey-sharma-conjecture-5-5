import PrimePowerRoots

/-! The precise additional root theorems needed to replace the comparison bijection.
The Frobenius divisibility and exact-root subgroup assertions remain explicit inputs. -/
namespace Conjecture55Frobenius
universe u

def RootDivisibilityInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], ∀ n : ℕ, n ∣ Nat.card G →
    n ∣ Nat.card {x : G // x ^ n = 1}

def ExactRootSubgroupInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], ∀ n : ℕ, n ∣ Nat.card G →
    Nat.card {x : G // x ^ n = 1} = n →
      ∃ N : Subgroup G, Nat.card N = n ∧ ∀ x : G, x ^ n = 1 → x ∈ N

/-- The ordinary Frobenius lower bound follows from its divisibility statement. -/
theorem root_lower_bound_of_divisibility
    (hdiv : RootDivisibilityInput.{u})
    {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : n ∣ Nat.card G) :
    n ≤ Nat.card {x : G // x ^ n = 1} := by
  let : Nonempty {x : G // x ^ n = 1} := ⟨⟨1, one_pow n⟩⟩
  exact Nat.le_of_dvd Nat.card_pos (hdiv G n hn)

/-- The doubled bound requires the exact-root subgroup theorem in addition
 to Frobenius divisibility; the obstruction is an actual noncyclic subgroup. -/
theorem doubled_root_bound_of_frobenius_inputs
    (hdiv : RootDivisibilityInput.{u}) (hexact : ExactRootSubgroupInput.{u})
    {G : Type u} [Group G] [Finite G] {p r j d : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hH : Nat.card H = p ^ r) (hnc : ¬IsCyclic H)
    (hrj : r ≤ j + 1) (hbig : p ^ (j + 1) ∣ Nat.card G)
    (hsmall : p ^ j * d ∣ Nat.card G) (hpd : ¬p ∣ d) :
    2 * (p ^ j * d) ≤ Nat.card {x : G // x ^ (p ^ j * d) = 1} := by
  let n := p ^ j * d
  have hn : 0 < n := Nat.pos_of_dvd_of_pos hsmall Nat.card_pos
  have hlo := root_lower_bound_of_divisibility hdiv n hsmall
  have hrootdiv := hdiv G n hsmall
  obtain ⟨k, hk⟩ := hrootdiv
  by_contra hbound
  have hlt : Nat.card {x : G // x ^ n = 1} < 2 * n := Nat.lt_of_not_ge hbound
  have hklt : k < 2 := by nlinarith
  have hkpos : 0 < k := by nlinarith
  have hkone : k = 1 := by omega
  have heq : Nat.card {x : G // x ^ n = 1} = n := by simpa [hkone] using hk
  obtain ⟨N, hN, hroots⟩ := hexact G n hsmall heq
  exact AmiriNext.no_subgroup_of_card_eq_exponent_contains_all_roots
    hp H hH hnc hrj hbig hpd N hN hroots

/-- Specialize the genuine noncyclic-subgroup obstruction to an actual Klein-four
subgroup and all relevant divisors of the odd part. -/
theorem double_root_bounds_of_klein_four
    (hdiv : RootDivisibilityInput.{u}) (hexact : ExactRootSubgroupInput.{u})
    {G : Type u} [Group G] [Finite G] (a m : ℕ)
    (hm : Odd m) (hcard : Nat.card G = 2 ^ a * m)
    (E : Subgroup G) (hE : Nat.card E = 4) (hEpow : ∀ x : E, x ^ 2 = 1) :
    ∀ d, d ∣ m → ∀ j, 1 ≤ j → j < a →
      2 ^ (j + 1) * d ≤ Nat.card {x : G // x ^ (2 ^ j * d) = 1} := by
  have hnc : ¬IsCyclic E := by
    intro h
    let : IsCyclic E := h
    have hd : Nat.card E ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hEpow
    norm_num [hE] at hd
  intro d hd j hj hja
  have hbig : 2 ^ (j + 1) ∣ Nat.card G := by
    rw [hcard]
    exact (pow_dvd_pow 2 (by omega : j + 1 ≤ a)).trans (dvd_mul_right _ _)
  have hsmall : 2 ^ j * d ∣ Nat.card G := by
    rw [hcard]
    exact mul_dvd_mul (pow_dvd_pow 2 (by omega : j ≤ a)) hd
  have hpd : ¬2 ∣ d := fun h => hm.not_two_dvd_nat (h.trans hd)
  have hb := doubled_root_bound_of_frobenius_inputs hdiv hexact Nat.prime_two E
    (by simpa using hE : Nat.card E = 2 ^ 2) hnc (by omega) hbig hsmall hpd
  simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hb

#print axioms double_root_bounds_of_klein_four
#print axioms root_lower_bound_of_divisibility
#print axioms doubled_root_bound_of_frobenius_inputs
end Conjecture55Frobenius
