import Conjecture55PSL2
import Families
import Arithmetic

namespace Conjecture55PSL2

/-- Concrete lower bound on the number of cyclic subgroups of PSL₂ over
any prime field of order at least five. -/
theorem psl2_cyclic_count_lower_bound {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    p ^ 2 + p + 2 ≤ Nat.card (CyclicSum.CyclicSubgroups (PSL2 p)) := by
  obtain ⟨U, hUcyc, hUcard, hUN⟩ := exists_split_torus_data hp
  obtain ⟨V, hVcyc, hVcard, hVN⟩ := exists_nonsplit_torus_data hp
  exact CyclicSum.cyclic_count_ge_psl2_families (Fact.out : p.Prime) hp U V
    hUcyc hVcyc hUcard hVcard hUN hVN (card_psl2 hp)
    (fun P => (sylow_cyclic_card P).2) (sylow_card_lower_bound hp)

/-- Every PSL₂ over a prime field of order at least five has at least the
cyclic-subgroup threshold appearing in Conjecture 5.5. -/
theorem psl2_fc_threshold_le_cyclic_count {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    2 ^ ((Nat.card (PSL2 p)).primeFactors.card + 2) ≤
      Nat.card (CyclicSum.CyclicSubgroups (PSL2 p)) := by
  calc
    2 ^ ((Nat.card (PSL2 p)).primeFactors.card + 2) ≤ p ^ 2 + p + 2 := by
      rw [card_psl2 hp]
      exact Conjecture55Arithmetic.psl2_primeFactor_threshold_le p Fact.out hp
    _ ≤ _ := psl2_cyclic_count_lower_bound hp

#print axioms psl2_cyclic_count_lower_bound
#print axioms psl2_fc_threshold_le_cyclic_count
end Conjecture55PSL2
