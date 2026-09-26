import Mathlib

/-!
The conjugation-injectivity proof is extracted verbatim from Qiuzhen-CFSG/CFSG,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd,
GorensteinWalter/PGammaL2NormalExtension.lean:59-89 (Apache-2.0).
-/
namespace Conjecture55OuterAut

theorem conjNormal_injective_of_centralizer_eq_bot
    {R : Type*} [Group R]
    (N : Subgroup R) [N.Normal]
    (hC : Subgroup.centralizer (N : Set R) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := N)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  have hker : Subgroup.centralizer (N : Set R) =
      (MulAut.conjNormal (H := N)).ker := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg
      ext x
      rw [MulAut.conjNormal_apply]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hg) (x : R) x.2
      calc
        g * (x : R) * g⁻¹ = ((x : R) * g) * g⁻¹ := by rw [hcomm]
        _ = x := by group
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hval := congrArg (fun y : N => (y : R))
        (DFunLike.congr_fun hg ⟨x, hx⟩)
      change g * x * g⁻¹ = x at hval
      calc
        x * g = (g * x * g⁻¹) * g := by rw [hval]
        _ = g * x := by group
  rw [← hker, hC]

/-- A normal subgroup with trivial ambient centralizer has index dividing the
ratio between its automorphism-group order and its own order. -/
lemma normal_index_dvd_of_aut_card
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [S.Normal]
    (hC : Subgroup.centralizer (S : Set G) = ⊥) (k : ℕ)
    (hAut : Nat.card (MulAut S) = k * Nat.card S) : S.index ∣ k := by
  have hdiv := Subgroup.card_dvd_of_injective
    (MulAut.conjNormal (H := S)) (conjNormal_injective_of_centralizer_eq_bot S hC)
  rw [hAut] at hdiv
  rcases hdiv with ⟨m, hm⟩
  refine ⟨m, Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card S) ?_⟩
  calc
    k * Nat.card S = Nat.card G * m := hm
    _ = (S.index * m) * Nat.card S := by rw [← S.index_mul_card]; ac_rfl

#print axioms normal_index_dvd_of_aut_card
end Conjecture55OuterAut
