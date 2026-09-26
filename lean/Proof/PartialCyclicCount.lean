import RootWeights
import RootDivisibilityInput
import ComparisonRoots

/-! Partial cyclic-subgroup counts from ordinary Frobenius divisibility. -/

open scoped BigOperators

namespace Conjecture55PartialCount
open Conjecture55Lean4Web.CyclicSum
noncomputable section
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [Fintype G]

/-- Cyclic subgroups whose order divides the specified integer. -/
abbrev CyclicDividing (G : Type*) [Group G] (n : ℕ) :=
  {K : CyclicSubgroups G // Nat.card K.1 ∣ n}

def generatedRoot {n : ℕ} (x : {x : G // x ^ n = 1}) : CyclicDividing G n :=
  ⟨generated x.1, by
    change Nat.card (Subgroup.zpowers x.1) ∣ n
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one x.2⟩

def generatorFiberEquiv {n : ℕ} (K : CyclicDividing G n) :
    {x : {x : G // x ^ n = 1} // generatedRoot x = K} ≃
      {x : G // generated x = K.1} where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  invFun x := ⟨⟨x.1, by
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h := congrArg (fun L : CyclicSubgroups G => Nat.card L.1) x.2
    change Nat.card (Subgroup.zpowers x.1) = Nat.card K.1.1 at h
    rw [Nat.card_zpowers] at h
    exact h ▸ K.2⟩, Subtype.ext x.2⟩
  left_inv _x := Subtype.ext (Subtype.ext rfl)
  right_inv _x := Subtype.ext rfl

theorem card_generatedRoot_fiber {n : ℕ} (K : CyclicDividing G n) :
    Nat.card {x : {x : G // x ^ n = 1} // generatedRoot x = K} =
      (Nat.card K.1.1).totient := by
  rw [Nat.card_congr (generatorFiberEquiv K), card_generated_fiber]

theorem cyclicDividing_count_eq_sum (n : ℕ) :
    (Nat.card (CyclicDividing G n) : ℚ) =
      ∑ x : {x : G // x ^ n = 1}, (1 : ℚ) / (orderOf x.1).totient := by
  classical
  rw [← Fintype.sum_fiberwise (generatedRoot (G := G) (n := n))]
  calc
    (Nat.card (CyclicDividing G n) : ℚ) = ∑ _K : CyclicDividing G n, (1 : ℚ) := by
      simp [Nat.card_eq_fintype_card]
    _ = ∑ K : CyclicDividing G n,
        ∑ x : {x : {x : G // x ^ n = 1} // generatedRoot x = K},
          (1 : ℚ) / (orderOf x.1.1).totient := by
      apply Fintype.sum_congr
      intro K
      have hx (x : {x : {x : G // x ^ n = 1} // generatedRoot x = K}) :
          orderOf x.1.1 = Nat.card K.1.1 := by
        have h := congrArg (fun L : CyclicDividing G n => Nat.card L.1.1) x.2
        simpa only [generatedRoot, generated, Nat.card_zpowers] using h
      simp_rw [hx]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, card_generatedRoot_fiber]
      have hpos : 0 < (Nat.card K.1.1).totient := Nat.totient_pos.mpr Nat.card_pos
      field_simp

def nestedRootsEquiv {n d : ℕ} (hd : d ∣ n) :
    {x : {x : G // x ^ n = 1} // x.1 ^ d = 1} ≃ {x : G // x ^ d = 1} where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_of_pow_eq_one x.2).trans hd)⟩, x.2⟩
  left_inv _x := Subtype.ext (Subtype.ext rfl)
  right_inv _x := Subtype.ext rfl

theorem cyclicDividing_count_eq_unit_average (n : ℕ) [NeZero n] :
    (Nat.card (CyclicDividing G n) : ℚ) =
      (∑ u : (ZMod n)ˣ,
        (Nat.card {x : G // x ^ RootWeights.rootDivisor n u = 1} : ℚ)) / n.totient := by
  classical
  rw [cyclicDividing_count_eq_sum]
  have hav (x : {x : G // x ^ n = 1}) :=
    RootWeights.reciprocal_totient_eq_unit_average
      (n := n) (orderOf_dvd_of_pow_eq_one x.2)
  simp_rw [hav]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [orderOf_dvd_iff_pow_eq_one]
  rw [← Nat.card_congr (nestedRootsEquiv (G := G) (RootWeights.rootDivisor_dvd n u))]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Ordinary Frobenius root divisibility already suffices for this partial
cyclic-subgroup count; no exact-root subgroup theorem is assumed. -/
theorem divisors_card_le_cyclicDividing {n : ℕ} (hn : n ∣ Nat.card G) :
    n.divisors.card ≤ Nat.card (CyclicDividing G n) := by
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hn Nat.card_pos
  let : NeZero n := ⟨hnpos.ne'⟩
  let H := Multiplicative (ZMod n)
  have hH : ∀ x : H, orderOf x ∣ n := by
    intro x
    simpa [H] using orderOf_dvd_natCard x
  have hq : (Nat.card (CyclicSubgroups H) : ℚ) ≤
      (Nat.card (CyclicDividing G n) : ℚ) := by
    rw [RootWeights.cyclic_count_eq_unit_average hH, cyclicDividing_count_eq_unit_average]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro u _
    have hd := RootWeights.rootDivisor_dvd n u
    rw [RootWeights.card_roots_cyclic]
    simp only [H, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card, Nat.gcd_eq_right hd]
    exact Nat.cast_le.mpr (by simpa only [Nat.card_eq_fintype_card] using
      Conjecture55FrobeniusProof.rootCountLowerBound G _ (hd.trans hn))
  rw [cyclic_count_eq_divisors_card] at hq
  simpa [H] using (show (Nat.card H).divisors.card ≤
    Nat.card (CyclicDividing G n) from by exact_mod_cast hq)

#print axioms cyclicDividing_count_eq_sum
#print axioms cyclicDividing_count_eq_unit_average
#print axioms divisors_card_le_cyclicDividing
end
end Conjecture55PartialCount
