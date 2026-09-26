import Brauer
import CountFibers

noncomputable section
namespace Conjecture55FrobeniusProof
open Function
variable {G : Type*} [Group G]

def powerTail (H : Subgroup G) (x : G) : ℤ → G ⧸ H := fun k => ↑(x ^ k)

def powerCore (H : Subgroup G) (x : G) : Subgroup G where
  carrier := {h | ∀ k : ℤ, (x ^ k)⁻¹ * h * x ^ k ∈ H}
  one_mem' := by intro k; simpa using H.one_mem
  mul_mem' := by
    intro a b ha hb k
    have ht := H.mul_mem (ha k) (hb k)
    convert ht using 1 <;> group
  inv_mem' := by
    intro a ha k
    have ht := H.inv_mem (ha k)
    convert ht using 1 <;> group

theorem powerCore_le (H : Subgroup G) (x : G) : powerCore H x ≤ H := by
  intro h hh
  simpa using hh 0

theorem mem_normalizer_powerCore (H : Subgroup G) (x : G) :
    x ∈ Subgroup.normalizer (powerCore H x : Set G) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro h
  constructor
  · intro hh k
    have ht := hh (k - 1)
    convert ht using 1 <;> simp only [zpow_sub, zpow_one] <;> group
  · intro hh k
    have ht := hh (k + 1)
    convert ht using 1 <;> simp only [zpow_add, zpow_one] <;> group

theorem tail_eq_implies_core (H : Subgroup G) (x y : G)
    (hxy : powerTail H x = powerTail H y) :
    x⁻¹ * y ∈ powerCore H x := by
  intro k
  have hk : (y ^ k)⁻¹ * x ^ k ∈ H :=
    QuotientGroup.eq.mp ((congrFun hxy k).symm)
  have hk1 : (x ^ (k + 1))⁻¹ * y ^ (k + 1) ∈ H :=
    QuotientGroup.eq.mp (congrFun hxy (k + 1))
  have ht := H.mul_mem hk1 hk
  convert ht using 1 <;> simp only [zpow_add, zpow_one] <;> group

theorem tail_conj (H : Subgroup G) (h : H) (x : G) :
    powerTail H ((h : G) * x * (h : G)⁻¹) = h • powerTail H x := by
  funext k
  change (↑(((h : G) * x * (h : G)⁻¹) ^ k) : G ⧸ H) = ↑((h : G) * x ^ k)
  rw [conj_zpow]
  exact QuotientGroup.mk_mul_of_mem _ (H.inv_mem h.prop)

theorem pow_mul_eq_one_of_mem_normalizer (U : Subgroup G) [Finite U]
    {n : ℕ} (hn : Nat.card U ∣ n) (v : G) (hv : v ^ n = 1)
    (hvU : v ∈ Subgroup.normalizer (U : Set G)) (u : U) :
    (v * (u : G)) ^ n = 1 := by
  classical
  let V := Subgroup.normalizer (U : Set G)
  let W : Subgroup V := U.subgroupOf V
  let v' : V := ⟨v, hvU⟩
  let u' : W := ⟨⟨u.val, U.le_normalizer u.prop⟩, u.prop⟩
  letI : Finite W := Finite.of_equiv U
    (Subgroup.subgroupOfEquivOfLe U.le_normalizer).toEquiv.symm
  letI := Fintype.ofFinite W
  have hwcard : Fintype.card W = Nat.card U := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe U.le_normalizer).toEquiv
  have hv' : v' ^ n = 1 := Subtype.ext hv
  have ht := pow_mul_eq_one_of_normal_card_dvd W (hwcard ▸ hn) v' hv' u'
  exact congrArg (fun z : V => (z : G)) ht

theorem tail_mul_core (H : Subgroup G) (x : G) (h : powerCore H x) :
    powerTail H (x * (h : G)) = powerTail H x := by
  let U := powerCore H x
  let V := Subgroup.normalizer (U : Set G)
  let W : Subgroup V := U.subgroupOf V
  let x' : V := ⟨x, mem_normalizer_powerCore H x⟩
  let h' : V := ⟨h.val, U.le_normalizer h.prop⟩
  have hh' : QuotientGroup.mk' W h' = 1 := by
    exact (QuotientGroup.eq_one_iff h').mpr (show h' ∈ W from h.prop)
  funext k
  have he : QuotientGroup.mk' W ((x' * h') ^ k) = QuotientGroup.mk' W (x' ^ k) := by
    simp only [map_zpow, map_mul, hh', mul_one]
  have hm : (((x' * h') ^ k)⁻¹ * x' ^ k) ∈ W := QuotientGroup.eq.mp he
  apply QuotientGroup.eq.mpr
  exact powerCore_le H x hm

theorem tail_eq_iff_core (H : Subgroup G) (x y : G) :
    powerTail H x = powerTail H y ↔ x⁻¹ * y ∈ powerCore H x := by
  constructor
  · exact tail_eq_implies_core H x y
  · intro h
    have ht := tail_mul_core H x ⟨x⁻¹ * y, h⟩
    simpa only [mul_inv_cancel_left] using ht.symm

#print axioms powerCore_le
#print axioms mem_normalizer_powerCore
#print axioms tail_eq_implies_core
#print axioms tail_conj
#print axioms pow_mul_eq_one_of_mem_normalizer
#print axioms tail_mul_core
#print axioms tail_eq_iff_core
end Conjecture55FrobeniusProof
