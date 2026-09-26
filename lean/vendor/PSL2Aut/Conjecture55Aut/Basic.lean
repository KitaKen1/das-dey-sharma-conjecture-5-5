module
public import Mathlib
noncomputable section
open Matrix
namespace Conjecture55Aut
universe u
/-- `PSL(2,K)`. -/
public abbrev PSL2 (K : Type u) [CommRing K] :=
  ProjectiveSpecialLinearGroup (Fin 2) K

/-- `PGL(2,K)`. -/
public abbrev PGL2 (K : Type u) [CommRing K] :=
  ProjGenLinGroup (Fin 2) K

/-- A positive power of an odd prime.  This is the `q` occurring in the
definition of a `D`-group. -/
@[expose] public def IsOddPrimePower (q : ℕ) : Prop :=
  ∃ p n : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ n ∧ q = p ^ n


end Conjecture55Aut
