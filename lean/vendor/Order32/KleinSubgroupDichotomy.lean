import Mathlib

namespace Conjecture55Semidihedral

/-- A finite element-generation certificate turns a Klein-four embedding
into an actual subgroup dichotomy. No classification input is assumed. -/
theorem subgroup_le_ker_or_eq_top
    {M E B : Type*} [Group M] [Finite M] [Group E] [Finite E] [Group B] [DecidableEq B]
    (π ρ : M →* B)
    (hroot : Nat.card {x : M // x ^ 2 = 1 ∧ ρ x = 1} = 2)
    (n : ℕ)
    (hgen : ∀ y z : M, π y ≠ 1 → z ^ 2 = 1 → ρ z ≠ 1 →
      ∀ g : M, ∃ i : Fin n, ∃ j : Fin 2,
        g = (if ρ y = 1 then y else y * z) ^ i.val * z ^ j.val)
    (H : Subgroup M) (f : E →* H) (hf : Function.Injective f)
    (hE : Nat.card E = 4) (hsq : ∀ x : E, x ^ 2 = 1) :
    H ≤ π.ker ∨ H = ⊤ := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : E, ρ (f z : M) ≠ 1 := by
    by_contra hn
    push Not at hn
    let j : E → {x : M // x ^ 2 = 1 ∧ ρ x = 1} := fun z =>
      ⟨f z, ⟨by change (((f z) ^ 2 : H) : M) = 1; rw [← map_pow, hsq z, map_one]; rfl,
        hn z⟩⟩
    have hj : Function.Injective j := fun x y h =>
      hf (Subtype.ext (show (f x : M) = (f y : M) from
        congrArg (fun v : {x : M // x ^ 2 = 1 ∧ ρ x = 1} => v.val) h))
    have hc := Nat.card_le_card_of_injective j hj
    rw [hE, hroot] at hc
    omega
  by_cases hle : H ≤ π.ker
  · exact Or.inl hle
  · right
    obtain ⟨y, hy, hπ⟩ := SetLike.not_le_iff_exists.mp hle
    have hyπ : π y ≠ 1 := hπ
    have hzsq : (f z : M) ^ 2 = 1 := by
      change (((f z) ^ 2 : H) : M) = 1
      rw [← map_pow, hsq z, map_one]
      rfl
    apply (Subgroup.eq_top_iff' H).mpr
    intro g
    obtain ⟨i, j, hg⟩ := hgen y (f z) hyπ hzsq hz g
    rw [hg]
    apply H.mul_mem
    · apply H.pow_mem
      split_ifs
      · exact hy
      · exact H.mul_mem hy (f z).property
    · exact H.pow_mem (f z).property _

#print axioms subgroup_le_ker_or_eq_top
end Conjecture55Semidihedral
