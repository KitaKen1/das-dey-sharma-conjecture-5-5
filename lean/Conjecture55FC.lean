import FormalConjectures.Arxiv.«2604.08040».Conjecture5_5
import Conjecture55ProofEndpoint

/-!
# Das–Dey–Sharma Conjecture 5.5: exact Formal Conjectures target

The proof is developed independently of the upstream placeholder.  This file
applies the checked modular endpoint to the actual Formal Conjectures
definitions and supplies the affirmative answer `True`.
-/

namespace Arxiv.«2604.08040»

/-- The solved form of the exact Formal Conjectures target. -/
theorem solvable_of_cyc_lt_solved :
    answer(True) ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  Conjecture55Lean4Web.solvable_of_cyc_lt

#print axioms solvable_of_cyc_lt_solved

end Arxiv.«2604.08040»
