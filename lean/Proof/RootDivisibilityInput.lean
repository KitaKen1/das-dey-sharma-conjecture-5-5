import Frobenius
import FrobeniusBridge

namespace Conjecture55FrobeniusProof
universe u

/-- Discharges the precise universal input used by the existing root assembly. -/
theorem provedRootDivisibilityInput : Conjecture55Frobenius.RootDivisibilityInput.{u} :=
  frobenius_root_divisibility

theorem rootCountLowerBound (G : Type u) [Group G] [Finite G] (n : ℕ)
    (hn : n ∣ Nat.card G) : n ≤ Nat.card {x : G // x ^ n = 1} :=
  Conjecture55Frobenius.root_lower_bound_of_divisibility
    provedRootDivisibilityInput n hn

#print axioms provedRootDivisibilityInput
#print axioms rootCountLowerBound
end Conjecture55FrobeniusProof
