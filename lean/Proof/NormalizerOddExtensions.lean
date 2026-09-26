import CyclicExtensions

/-! Odd cyclic subgroups of a normalizer commute with its cyclic 2-subgroup. -/

namespace Conjecture55NormalizerOdd
open Conjecture55PartialCount Conjecture55CyclicExtensions
open Conjecture55Lean4Web.CyclicSum
noncomputable section
variable {G : Type*} [Group G] [Finite G]

theorem odd_normalizer_subgroup_le_centralizer
    (A : Subgroup G) [IsCyclic A] {j : ℕ} (hA : Nat.card A = 2 ^ (j + 1))
    (K : Subgroup (Subgroup.normalizer (A : Set G))) (hK : Odd (Nat.card K)) :
    K.map (Subgroup.normalizer (A : Set G)).subtype ≤ Subgroup.centralizer (A : Set G) := by
  let f := A.normalizerMonoidHom.comp K.subtype
  have hAut : Nat.card (MulAut A) = 2 ^ j := by
    rw [IsCyclic.card_mulAut, hA, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  have hcop : (Nat.card K).Coprime (Nat.card (MulAut A)) := by
    rw [hAut]
    exact hK.coprime_two_right.pow_right j
  have hf (k : K) : f k = 1 := by
    have hpow : (f k) ^ Nat.card K = 1 := by
      rw [← map_pow]
      rw [orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard k), map_one]
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hpow)
      (orderOf_dvd_natCard (f k))
  rintro x ⟨k, hk, rfl⟩
  have hmem : k ∈ A.normalizerMonoidHom.ker := hf ⟨k, hk⟩
  rwa [Subgroup.normalizerMonoidHom_ker] at hmem

def oddFactor (A : Subgroup G) {c : ℕ}
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) : Subgroup G :=
  K.1.1.map (Subgroup.normalizer (A : Set G)).subtype

theorem oddFactor_card (A : Subgroup G) {c : ℕ}
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    Nat.card (oddFactor A K) = Nat.card K.1.1 := by
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

theorem oddFactor_isCyclic (A : Subgroup G) {c : ℕ}
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) : IsCyclic (oddFactor A K) := by
  exact (Conjecture55Lean4Web.cyclicSubgroupMap
    (Subgroup.normalizer (A : Set G)).subtype K.1).2

theorem oddFactor_odd (A : Subgroup G) {c : ℕ} (hc : Odd c)
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) : Odd (Nat.card (oddFactor A K)) := by
  rw [oddFactor_card]
  exact Odd.of_dvd_nat hc K.2

theorem oddFactor_commutes (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    ∀ a : A, ∀ b : oddFactor A K, Commute (a : G) (b : G) := by
  have hle := odd_normalizer_subgroup_le_centralizer A hA K.1.1 (Odd.of_dvd_nat hc K.2)
  intro a b
  exact (Subgroup.mem_centralizer_iff.mp (hle b.2)) a.1 a.2

def extendOdd (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) : CyclicSubgroups G :=
  ⟨A ⊔ oddFactor A K, by
    let : IsCyclic (oddFactor A K) := oddFactor_isCyclic A K
    apply cyclic_sup_of_commuting_coprime _ _ (oddFactor_commutes A hA hc K)
    rw [hA]
    exact (oddFactor_odd A hc K).coprime_two_left.pow_left (j + 1)⟩

theorem extendOdd_card (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c)
    (K : CyclicDividing (Subgroup.normalizer (A : Set G)) c) :
    Nat.card (extendOdd A hA hc K).1 = 2 ^ (j + 1) * Nat.card K.1.1 := by
  change Nat.card (A ⊔ oddFactor A K : Subgroup G) = _
  rw [card_sup_of_commuting_coprime _ _ (oddFactor_commutes A hA hc K) (by
    rw [hA]; exact (oddFactor_odd A hc K).coprime_two_left.pow_left (j + 1)),
    hA, oddFactor_card]

theorem extendOdd_injective (A : Subgroup G) [IsCyclic A] {j c : ℕ}
    (hA : Nat.card A = 2 ^ (j + 1)) (hc : Odd c) :
    Function.Injective (extendOdd A hA hc) := by
  intro K L he
  have hcard := congrArg (fun H : CyclicSubgroups G => Nat.card H.1) he
  rw [extendOdd_card, extendOdd_card] at hcard
  have hKL : Nat.card K.1.1 = Nat.card L.1.1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hcard
  have hH : (extendOdd A hA hc K).1 = (extendOdd A hA hc L).1 := congrArg Subtype.val he
  let H := (extendOdd A hA hc K).1
  let : IsCyclic H := (extendOdd A hA hc K).2
  have hleL : oddFactor A L ≤ H := by rw [show H = (extendOdd A hA hc L).1 from hH]; exact le_sup_right
  have hB : oddFactor A K = oddFactor A L :=
    subgroups_eq_in_cyclic _ _ H le_sup_right hleL (by rw [oddFactor_card, oddFactor_card, hKL])
  apply Subtype.ext
  apply Subtype.ext
  exact Subgroup.map_injective (Subgroup.subtype_injective _) hB

#print axioms odd_normalizer_subgroup_le_centralizer
#print axioms oddFactor_commutes
#print axioms extendOdd_card
#print axioms extendOdd_injective
end
end Conjecture55NormalizerOdd
