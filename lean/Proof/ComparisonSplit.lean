import Conjecture55Foundation

/-! Split the supplied cyclic comparison group and close the exponent-two Sylow branch. -/

namespace Conjecture55ComparisonSplit
open Conjecture55Lean4Web

/-- A cyclic group of order four times an odd number splits into its
four-part and odd part. The isomorphism is constructed from the cardinality. -/
noncomputable def cyclic_four_odd_equiv
    {K : Type*} [Group K] [Fintype K] [IsCyclic K]
    (m : ℕ) (hm : Odd m) (hK : Nat.card K = 4 * m) :
    K ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod m) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm.pos⟩
  have hc : (Nat.card (Multiplicative (ZMod 4))).Coprime
      (Nat.card (Multiplicative (ZMod m))) := by
    simpa using hm.coprime_two_left.pow_left 2
  let : IsCyclic (Multiplicative (ZMod 4) × Multiplicative (ZMod m)) :=
    Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, hc⟩
  exact mulEquivOfCyclicCardEq (by simpa using hK)

/-- Regroup the actual comparison group as an order-eight factor times
its cyclic odd part. -/
noncomputable def comparison_split_equiv
    {K H : Type*} [Group K] [Group H] [Fintype K] [IsCyclic K]
    (m : ℕ) (hm : Odd m) (hK : Nat.card K = 4 * m) :
    K × H ≃* (Multiplicative (ZMod 4) × H) × Multiplicative (ZMod m) := by
  let e := cyclic_four_odd_equiv m hm hK
  exact {
    toFun := fun x => ((e x.1 |>.1, x.2), e x.1 |>.2)
    invFun := fun x => (e.symm (x.1.1, x.2), x.1.2)
    left_inv := by rintro ⟨k, h⟩; simp
    right_inv := by rintro ⟨⟨z, h⟩, c⟩; simp
    map_mul' := by rintro ⟨k, h⟩ ⟨k', h'⟩; simp
  }

/-- The exponent-two Sylow branch directly from the original cyclic
comparison group, with no splitting hypothesis. -/
theorem lower_bound_of_cyclic_comparison_and_sylow_exponent_two
    {G K H : Type*} [Group G] [Group K] [Group H]
    [Fintype G] [Fintype K] [Fintype H] [IsCyclic K]
    (m : ℕ) (hm : Odd m) (hK : Nat.card K = 4 * m) (hH : Nat.card H = 2)
    (P : Sylow 2 G) (hP : ∀ x : P, x ^ 2 = 1)
    (e : G ≃ K × H) (he : ∀ x : G, orderOf x ∣ orderOf (e x)) :
    2 ^ ((Nat.card G).primeFactors.card + 2) ≤ cyc G := by
  let : NeZero m := ⟨Nat.ne_of_gt hm.pos⟩
  let s := comparison_split_equiv (H := H) m hm hK
  have hBcard : Nat.card (Multiplicative (ZMod 4) × H) = 8 := by
    rw [Nat.card_prod, hH]
    norm_num
  have hB : ∀ b : Multiplicative (ZMod 4) × H, b ^ 4 = 1 := by
    rintro ⟨z, h⟩
    apply Prod.ext
    · change z ^ 4 = 1
      simpa using (pow_card_eq_one' (x := z))
    · change h ^ 4 = 1
      have h2 : h ^ 2 = 1 := by rw [← hH]; exact pow_card_eq_one'
      calc
        h ^ 4 = (h ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [h2, one_pow]
  apply ElementaryBound.lower_bound_of_sylow_exponent_two_comparison P hP hBcard hB
    (by simpa using hm) (e.trans s.toEquiv)
  intro g
  change orderOf g ∣ orderOf (s (e g))
  simpa only [s.orderOf_eq] using he g

/-- The preceding bound using the exact Formal Conjectures definitions. -/
theorem fc_lower_bound_of_cyclic_comparison_and_sylow_exponent_two
    {G K H : Type*} [Group G] [Group K] [Group H]
    [Fintype G] [Fintype K] [Fintype H] [IsCyclic K]
    (m : ℕ) (hm : Odd m) (hK : Nat.card K = 4 * m) (hH : Nat.card H = 2)
    (P : Sylow 2 G) (hP : ∀ x : P, x ^ 2 = 1)
    (e : G ≃ K × H) (he : ∀ x : G, orderOf x ∣ orderOf (e x)) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  simpa only [numPrimeFactors, Nat.card_eq_fintype_card] using
    lower_bound_of_cyclic_comparison_and_sylow_exponent_two m hm hK hH P hP e he

#print axioms cyclic_four_odd_equiv
#print axioms comparison_split_equiv
#print axioms lower_bound_of_cyclic_comparison_and_sylow_exponent_two
#print axioms fc_lower_bound_of_cyclic_comparison_and_sylow_exponent_two
end Conjecture55ComparisonSplit
