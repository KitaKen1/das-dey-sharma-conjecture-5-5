import TransferCharacter

/-! An invariant surjective C2 character of a Sylow subgroup lifts to an
index-two normal subgroup, with an explicitly identified Sylow subgroup. -/
namespace Conjecture55TransferCharacter
open Subgroup

variable {G : Type*} [Group G] [Finite G]

lemma exists_normal_index_two_of_character
    (P : Sylow 2 G) (f : P →* C2) (hf : Function.Surjective f)
    (hconj : ∀ (x y : P) (g : G), (y : G) = g⁻¹ * (x : G) * g → f y = f x) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧
      ∃ Q : Sylow 2 N, Nonempty (Q ≃* f.ker) ∧ Q.index = P.index := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : G →* C2 := MonoidHom.transfer f
  have hT (x : P) : T (x : G) = f x := transfer_restrict_eq P f hconj x
  have hsurj : Function.Surjective T := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨(x : G), (hT x).trans hx⟩
  let N : Subgroup G := T.ker
  have hNindex : N.index = 2 := by
    change T.ker.index = 2
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hfindex : f.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  let j : f.ker →* N :=
    { toFun := fun x => ⟨(x.val : G), (hT x.val).trans x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N => (z : G)) h
  let e : f.ker ≃* j.range := MonoidHom.ofInjective hj
  have hRcard : Nat.card j.range = Nat.card f.ker := Nat.card_congr e.symm.toEquiv
  have hfcard := f.ker.card_mul_index
  rw [hfindex] at hfcard
  have hNcard := N.card_mul_index
  rw [hNindex] at hNcard
  have hPcard := (P : Subgroup G).card_mul_index
  have hRmul := j.range.card_mul_index
  rw [hRcard] at hRmul
  have hRindex : j.range.index = P.index := by
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    nlinarith
  have hRgroup : IsPGroup 2 j.range :=
    (P.isPGroup'.to_subgroup f.ker).of_equiv e
  let Q : Sylow 2 N := hRgroup.toSylow (hRindex ▸ P.not_dvd_index)
  exact ⟨N, inferInstance, hNindex, Q, ⟨e.symm⟩, hRindex⟩

#print axioms exists_normal_index_two_of_character
end Conjecture55TransferCharacter
