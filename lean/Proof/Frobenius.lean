import TailFibers

namespace Conjecture55FrobeniusProof
universe u

/-- Frobenius root-count divisibility for arbitrary finite groups. -/
theorem frobenius_root_divisibility (G : Type u) [Group G] [Finite G]
    (n : ℕ) (hn : n ∣ Nat.card G) :
    n ∣ Nat.card {x : G // x ^ n = 1} := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (hpk.trans hn)
  have ht := subgroup_card_dvd_root_card H n (hH.symm ▸ hpk)
  simpa only [hH, Roots] using ht

#print axioms frobenius_root_divisibility
end Conjecture55FrobeniusProof
