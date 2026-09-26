import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic

namespace Conjecture55PSL2

lemma sylow_count_lower_bound {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime] (hpG : p < Nat.card G)
    (hP : ∀ P : Sylow p G, Nat.card P = p) :
    p + 1 ≤ Nat.card (Sylow p G) := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hn : Nat.card (Sylow p G) ≠ 1 := by
    intro hone
    letI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hone).1
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    rcases (Sylow.normal_of_subsingleton P).eq_bot_or_eq_top with hbot | htop
    · have hbad : Nat.card P = 1 := by change Nat.card (P : Subgroup G) = 1; rw [hbot]; simp
      have := hP P
      omega
    · have hbad : Nat.card P = Nat.card G := by
        change Nat.card (P : Subgroup G) = Nat.card G
        rw [htop]
        simp
      have := hP P
      omega
  have hmod : Nat.card (Sylow p G) % p = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using
      card_sylow_modEq_one p G
  by_contra h
  have hle : Nat.card (Sylow p G) ≤ p := by omega
  rcases hle.eq_or_lt with heq | hlt
  · simp [heq] at hmod
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    exact hn hmod

#print axioms sylow_count_lower_bound
end Conjecture55PSL2
