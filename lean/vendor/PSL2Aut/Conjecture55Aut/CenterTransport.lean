module
public import Conjecture55Aut.Basic
namespace Conjecture55Aut
universe u v
public lemma center_eq_bot_of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (hZ : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    rcases (e.surjective y) with ⟨z, hz⟩
    rw [← hz]
    simpa [map_mul] using congrArg e ((Subgroup.mem_center_iff.mp hx) z)
  have hx'' : e x = 1 := Subgroup.mem_bot.mp (by rwa [hZ] at hx')
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm 1 := by rw [hx'']
    _ = 1 := map_one e.symm

end Conjecture55Aut
