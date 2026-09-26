import Affine

namespace Conjecture55FrobeniusProof
open Function
variable {G : Type*} [Group G]

theorem affine_conj_iterate (U : Subgroup G) [U.Normal] (v : G) (u a : U) (k : ℕ) :
    (((affinePerm (MulAut.conjNormal v⁻¹) u : U → U)^[k]) a : G) =
      (v ^ k)⁻¹ * (a : G) * (v * (u : G)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', affinePerm_apply, Subgroup.coe_mul,
      MulAut.conjNormal_apply, inv_inv, ih, pow_succ, pow_succ, mul_inv_rev]
    group

/-- Brauer's finite-normal-subgroup power-conjugacy lemma. -/
theorem brauer_power_conjugacy (U : Subgroup G) [U.Normal] [Fintype U]
    (v : G) (u : U) :
    ∃ a : U, (a : G)⁻¹ * v ^ Fintype.card U * a =
      (v * (u : G)) ^ Fintype.card U := by
  classical
  obtain ⟨a, ha⟩ := exists_affine_periodic_card (MulAut.conjNormal v⁻¹) u
  have h := congrArg (fun a : U => (a : G)) ha
  rw [affine_conj_iterate] at h
  refine ⟨a, ?_⟩
  have hh := congrArg (fun z : G => (a : G)⁻¹ * v ^ Fintype.card U * z) h
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left] using hh.symm

theorem pow_mul_eq_one_of_normal_card_dvd (U : Subgroup G) [U.Normal] [Fintype U]
    {n : ℕ} (hn : Fintype.card U ∣ n) (v : G) (hv : v ^ n = 1) (u : U) :
    (v * (u : G)) ^ n = 1 := by
  obtain ⟨a, ha⟩ := brauer_power_conjugacy U v u
  have hc : IsConj (v ^ Fintype.card U) ((v * (u : G)) ^ Fintype.card U) :=
    isConj_iff.mpr ⟨(a : G)⁻¹, by simpa using ha⟩
  obtain ⟨k, hk⟩ := hn
  have hp := hc.pow k
  rw [← pow_mul, ← pow_mul, ← hk, hv] at hp
  exact isConj_one_right.mp hp

#print axioms affine_conj_iterate
#print axioms brauer_power_conjugacy
#print axioms pow_mul_eq_one_of_normal_card_dvd
end Conjecture55FrobeniusProof
