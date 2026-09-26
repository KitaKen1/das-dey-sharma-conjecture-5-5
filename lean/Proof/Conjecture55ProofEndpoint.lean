import SemidihedralCountingClosure

/-! Checked endpoint used by the exact Formal Conjectures wrapper. -/

namespace Conjecture55Lean4Web

/-- The exact affirmative target, including all finite groups. -/
theorem solvable_of_cyc_lt :
    True ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  Conjecture55CountingClosure.affirmative_target

#print axioms solvable_of_cyc_lt

end Conjecture55Lean4Web
