import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A character of a Sylow subgroup that is constant on ambient conjugacy
classes extends by transfer when its target has order two. -/
namespace Conjecture55TransferCharacter
open Subgroup MulAction

variable {G : Type*} [Group G] [Finite G]

lemma transfer_eq_pow_of_conjugacy_invariant
    {A : Type*} [CommGroup A] (H : Subgroup G) (f : H →* A)
    (hconj : ∀ (x y : H) (g : G), (y : G) = g⁻¹ * (x : G) * g → f y = f x)
    (x : H) : MonoidHom.transfer f (x : G) = f x ^ H.index := by
  classical
  letI : Fintype (Quotient (orbitRel (zpowers (x : G)) (G ⧸ H))) := Fintype.ofFinite _
  rw [index_eq_sum_minimalPeriod H x, ← Finset.prod_pow_eq_pow_sum,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  apply Finset.prod_congr rfl
  intro q _
  rw [← map_pow]
  exact hconj _ _ q.out.out rfl

abbrev C2 := Multiplicative (ZMod 2)

lemma c2_eq_of_one_iff (x y : C2) (h : x = 1 ↔ y = 1) : x = y := by
  have hfinite : ∀ a b : C2, (a = 1 ↔ b = 1) → a = b := by decide +kernel
  exact hfinite x y h

lemma c2_pow_odd (x : C2) {n : ℕ} (hn : Odd n) : x ^ n = x := by
  obtain ⟨k, rfl⟩ := hn
  have hx : x ^ 2 = 1 := by
    have h : ∀ a : C2, a ^ 2 = 1 := by decide +kernel
    exact h x
  simp [pow_add, pow_mul, hx]

lemma transfer_restrict_eq
    (P : Sylow 2 G) (f : P →* C2)
    (hconj : ∀ (x y : P) (g : G), (y : G) = g⁻¹ * (x : G) * g → f y = f x)
    (x : P) : MonoidHom.transfer f (x : G) = f x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [transfer_eq_pow_of_conjugacy_invariant (P : Subgroup G) f hconj]
  apply c2_pow_odd
  exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using P.not_dvd_index)

/-- If the kernel of a character to C2 is characterized by a power equation,
then the character is constant on ambient conjugacy classes in the subgroup. -/
lemma conjugacy_invariant_of_power_kernel
    (H : Subgroup G) (f : H →* C2) (n : ℕ)
    (hker : ∀ x : H, f x = 1 ↔ x ^ n = 1)
    (x y : H) (g : G) (hy : (y : G) = g⁻¹ * (x : G) * g) : f y = f x := by
  apply c2_eq_of_one_iff
  have horder : orderOf y = orderOf x := by
    calc
      orderOf y = orderOf (y : G) :=
        (orderOf_injective H.subtype H.subtype_injective y).symm
      _ = orderOf (x : G) := by
        rw [hy]
        simpa [MulAut.conj_apply] using
          orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective (x : G)
      _ = orderOf x := orderOf_injective H.subtype H.subtype_injective x
  rw [hker, hker, ← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one, horder]

#print axioms transfer_eq_pow_of_conjugacy_invariant
#print axioms c2_eq_of_one_iff
#print axioms c2_pow_odd
#print axioms transfer_restrict_eq
#print axioms conjugacy_invariant_of_power_kernel
end Conjecture55TransferCharacter
