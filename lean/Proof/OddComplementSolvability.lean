import Conjecture55Foundation
import FeitThompson.FinalTheorem

/-! The actual odd-order theorem removes the squarefree-index restriction
from the abelian Sylow normal-complement criterion. -/
namespace Conjecture55OddComplement
open Conjecture55Lean4Web

theorem isSolvable_of_aut_isTwoGroup
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) [IsMulCommutative P]
    (hAut : IsPGroup 2 (MulAut P)) : Group.IsSolvable G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN, hcomp⟩ := SylowInputs.exists_normal_complement_of_aut_isPGroup P hAut
  let : N.Normal := hN
  have hcard : Nat.card N = P.index := hcomp.index_eq_card.symm
  have hodd : Odd (Nat.card N) := by
    rw [hcard]
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using P.not_dvd_index)
  let : Group.IsSolvable N := odd_order_theorem N hodd
  let : Group.IsSolvable P := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  have hQ : Group.IsSolvable (G ⧸ N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := hcomp.symm.QuotientMulEquiv.toMonoidHom) hcomp.symm.QuotientMulEquiv.injective
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, hQ⟩

/-- Every finite group with Sylow two subgroup C4 × C2 is solvable,
with no restriction on the odd part of its order. -/
theorem isSolvable_of_c4c2_sylow
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (e : P ≃* Multiplicative (ZMod 4 × ZMod 2)) :
    Group.IsSolvable G := by
  let : IsMulCommutative P := IsMulCommutative.of_comm (fun x y => by
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _)
  exact isSolvable_of_aut_isTwoGroup P
    (Conjecture55C4C2.isPGroup_mulAut_of_equiv e)

#print axioms isSolvable_of_aut_isTwoGroup
#print axioms isSolvable_of_c4c2_sylow
end Conjecture55OddComplement
