import CyclicExtensions
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! Characteristic cyclic chains in large dihedral two-groups. -/

namespace Conjecture55CharacteristicChain
open Conjecture55CyclicExtensions
noncomputable section

theorem characteristic_comap_mulEquiv
    {G H : Type*} [Group G] [Group H] (K : Subgroup H) [K.Characteristic]
    (e : G ≃* H) : (K.comap e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  apply SetLike.ext
  intro x
  change e (φ x) ∈ K ↔ e x ∈ K
  let ψ : H ≃* H := e.symm.trans (φ.trans e)
  have hfix : K.comap ψ.toMonoidHom = K :=
    Subgroup.Characteristic.fixed (H := K) inferInstance ψ
  have hx := SetLike.ext_iff.mp hfix (e x)
  change ψ (e x) ∈ K ↔ e x ∈ K at hx
  simpa [ψ] using hx

theorem characteristic_map_mulEquiv
    {G H : Type*} [Group G] [Group H] (K : Subgroup G) [K.Characteristic]
    (e : G ≃* H) : (K.map e.toMonoidHom).Characteristic := by
  change (K.map (e : G →* H)).Characteristic
  rw [Subgroup.map_equiv_eq_comap_symm]
  exact characteristic_comap_mulEquiv K e.symm

theorem exists_characteristic_chain
    {G : Type*} [Group G] [Finite G]
    (R : Subgroup G) [IsCyclic R] [R.Characteristic]
    (h8 : 8 ∣ Nat.card R) :
    ∃ A : Fin 3 → Subgroup G, (∀ i, IsCyclic (A i)) ∧
      (∀ i, Nat.card (A i) = 2 ^ (i.val + 1)) ∧
      (∀ i, (A i).Characteristic) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hex (i : Fin 3) : ∃ B : Subgroup R, Nat.card B = 2 ^ (i.val + 1) := by
    apply Sylow.exists_subgroup_card_pow_prime
    exact (pow_dvd_pow 2 (by omega : i.val + 1 ≤ 3)).trans h8
  choose B hB using hex
  have hBchar (i : Fin 3) : (B i).Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    exact cyclic_subgroup_eq_of_card_eq _ _
      (Subgroup.card_map_of_injective φ.injective)
  let A (i : Fin 3) : Subgroup G := (B i).map R.subtype
  refine ⟨A, ?_, ?_, ?_⟩
  · intro i
    exact (Conjecture55Lean4Web.cyclicSubgroupMap R.subtype
      ⟨B i, inferInstance⟩).2
  · intro i
    exact (Subgroup.card_map_of_injective R.subtype_injective).trans (hB i)
  · intro i
    letI : (B i).Characteristic := hBchar i
    exact inferInstance

private theorem dihedralGroup_cases {n : ℕ} (x : DihedralGroup n) :
    (∃ i : ZMod n, x = DihedralGroup.r i) ∨
      ∃ i : ZMod n, x = DihedralGroup.sr i := by
  cases hx : DihedralGroup.equivSum x with
  | inl i =>
      left
      refine ⟨i, ?_⟩
      have h := (DihedralGroup.equivSum.symm_apply_apply x).symm
      rw [hx] at h
      simpa [DihedralGroup.equivSum] using h
  | inr i =>
      right
      refine ⟨i, ?_⟩
      have h := (DihedralGroup.equivSum.symm_apply_apply x).symm
      rw [hx] at h
      simpa [DihedralGroup.equivSum] using h

private theorem r_mem_rotation {n : ℕ} [NeZero n] (i : ZMod n) :
    DihedralGroup.r i ∈
      Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  refine ⟨i.val, ?_⟩
  change (DihedralGroup.r 1 : DihedralGroup n) ^ i.val = DihedralGroup.r i
  rw [DihedralGroup.r_one_pow]
  congr 1
  exact ZMod.natCast_zmod_val i

theorem dihedral_rotation_characteristic {l : ℕ} (hl : 2 ≤ l) :
    (Subgroup.zpowers (DihedralGroup.r 1 :
      DihedralGroup (2 ^ l))).Characteristic := by
  letI : NeZero (2 ^ l) := ⟨pow_ne_zero l (by norm_num)⟩
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, rfl⟩
  apply Subgroup.zpow_mem
  change φ (DihedralGroup.r 1) ∈
    Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ l))
  rcases dihedralGroup_cases (φ (DihedralGroup.r 1)) with ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [hi]
    exact r_mem_rotation i
  · have horder : orderOf (φ (DihedralGroup.r 1)) = 2 ^ l := by
      rw [MulEquiv.orderOf_eq φ, DihedralGroup.orderOf_r_one]
    rw [hi, DihedralGroup.orderOf_sr] at horder
    have hfour : 4 ≤ 2 ^ l := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hl
    omega

theorem dihedral_characteristic_chain {l : ℕ} (hl : 3 ≤ l) :
    ∃ A : Fin 3 → Subgroup (DihedralGroup (2 ^ l)),
      (∀ i, IsCyclic (A i)) ∧
      (∀ i, Nat.card (A i) = 2 ^ (i.val + 1)) ∧
      (∀ i, (A i).Characteristic) := by
  letI : NeZero (2 ^ l) := ⟨pow_ne_zero l (by norm_num)⟩
  let R : Subgroup (DihedralGroup (2 ^ l)) :=
    Subgroup.zpowers (DihedralGroup.r 1)
  letI : R.Characteristic := dihedral_rotation_characteristic (by omega)
  apply exists_characteristic_chain R
  change 8 ∣ Nat.card (Subgroup.zpowers
    (DihedralGroup.r 1 : DihedralGroup (2 ^ l)))
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  exact pow_dvd_pow 2 hl

#print axioms characteristic_comap_mulEquiv
#print axioms characteristic_map_mulEquiv
#print axioms exists_characteristic_chain
#print axioms dihedral_rotation_characteristic
#print axioms dihedral_characteristic_chain
end
end Conjecture55CharacteristicChain
