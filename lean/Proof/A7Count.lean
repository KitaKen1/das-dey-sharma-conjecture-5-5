import Conjecture55Foundation

/-! A lower bound for the actual A7 cyclic-subgroup count from its 7-cycles. -/
namespace Conjecture55A7Count
open Conjecture55Lean4Web Conjecture55Lean4Web
open scoped BigOperators

theorem cyclic_count_bound_of_constant_order_injection
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    (f : X → G) (hf : Function.Injective f) (n : ℕ)
    (horder : ∀ x, orderOf (f x) = n) :
    (Fintype.card X : ℚ) / n.totient ≤ cyc G := by
  classical
  have hs : (∑ g ∈ Finset.univ.image f, (1 : ℚ) / (orderOf g).totient) ≤
      ∑ g : G, (1 : ℚ) / (orderOf g).totient := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro g _ _
    positivity
  rw [Finset.sum_image (fun x _ y _ h => hf h)] at hs
  simpa only [horder, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div,
    ← cyc_eq_sum G] using hs

theorem card_seven_cycles :
    Nat.card {g : Equiv.Perm (Fin 7) // g.cycleType = {7}} = 720 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := Equiv.Perm.card_of_cycleType_singleton (α := Fin 7) (n := 7)
    (by decide) (by simp)
  norm_num at h
  exact h

theorem one_twenty_le_cyc_a7 : 120 ≤ cyc (alternatingGroup (Fin 7)) := by
  classical
  let X := {g : Equiv.Perm (Fin 7) // g.cycleType = {7}}
  let f : X → alternatingGroup (Fin 7) := fun g => ⟨g.val, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, g.prop]
    norm_num⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg
      (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) h)
  have horder : ∀ x : X, orderOf (f x) = 7 := by
    intro x
    rw [← Subgroup.orderOf_coe (f x)]
    change orderOf x.val = 7
    rw [← Equiv.Perm.lcm_cycleType, x.prop]
    simp
  have hb := cyclic_count_bound_of_constant_order_injection f hf 7 horder
  have hx : Fintype.card X = 720 := by
    simpa only [Nat.card_eq_fintype_card] using card_seven_cycles
  norm_num [hx, Nat.totient_prime (by decide : Nat.Prime 7)] at hb
  exact_mod_cast hb

theorem a7_fc_threshold_lt :
    2 ^ (numPrimeFactors (alternatingGroup (Fin 7)) + 2) <
      cyc (alternatingGroup (Fin 7)) := by
  have hnum : numPrimeFactors (alternatingGroup (Fin 7)) = 4 := by
    simp only [numPrimeFactors, ← Nat.card_eq_fintype_card, AlternatingSeven.card_a7]
    decide +kernel
  have hb := one_twenty_le_cyc_a7
  rw [hnum]
  norm_num
  omega

#print axioms cyclic_count_bound_of_constant_order_injection
#print axioms card_seven_cycles
#print axioms one_twenty_le_cyc_a7
#print axioms a7_fc_threshold_lt
end Conjecture55A7Count
