import PSL2Case
import PSL2AutCard
import OuterIndexCore

/-! The prime-field almost-simple case, using the actual checked automorphism theorem. -/

namespace Conjecture55Lean4Web

/-- The FC threshold holds for a finite group with a normal prime-field PSL₂
subgroup and trivial ambient centralizer. Its index bound is proved from the
actual automorphism-group order, rather than supplied as a hypothesis. -/
theorem threshold_le_of_normal_psl2_trivial_centralizer
    {G : Type*} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (S : Subgroup G) [S.Normal] (e : Conjecture55PSL2.PSL2 p ≃* S)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    2 ^ (numPrimeFactors G + 2) ≤ cyc G := by
  have hAutS : Nat.card (MulAut S) = 2 * Nat.card S := by
    calc
      Nat.card (MulAut S) = Nat.card (MulAut (Conjecture55PSL2.PSL2 p)) :=
        Nat.card_congr (MulAut.congr e).symm.toEquiv
      _ = 2 * Nat.card (Conjecture55PSL2.PSL2 p) :=
        Conjecture55OuterAut.card_mulAut_psl2 hp
      _ = 2 * Nat.card S := by rw [Nat.card_congr e.toEquiv]
  exact PSL2Extensions.fc_threshold_le_of_psl2_subgroup_index_one_or_two hp S e
    ((Nat.dvd_prime Nat.prime_two).mp
      (Conjecture55OuterAut.normal_index_dvd_of_aut_card S hC 2 hAutS))

#print axioms threshold_le_of_normal_psl2_trivial_centralizer

end Conjecture55Lean4Web
