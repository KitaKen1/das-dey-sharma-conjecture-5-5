import Theory.AutAlternating
import OuterIndexCore

namespace Conjecture55AlternatingAut
open Equiv

theorem card_mulAut_alternating (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) =
      2 * Nat.card (alternatingGroup (Fin n)) := by
  have hnpos : 0 < n := by omega
  letI : NeZero n := ⟨by omega⟩
  have hn1 : 1 < Fintype.card (Fin n) := by simpa using (show 1 < n by omega)
  letI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp hn1
  have h := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  calc
    Nat.card (MulAut (alternatingGroup (Fin n))) = Nat.card (Perm (Fin n)) :=
      (Nat.card_congr (Equiv.ofBijective _ h)).symm
    _ = 2 * Nat.card (alternatingGroup (Fin n)) :=
      two_mul_nat_card_alternatingGroup.symm

theorem normal_alternating_index_dvd_two
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [S.Normal]
    (hC : Subgroup.centralizer (S : Set G) = ⊥)
    (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : alternatingGroup (Fin n) ≃* S) : S.index ∣ 2 := by
  apply Conjecture55OuterAut.normal_index_dvd_of_aut_card S hC 2
  rw [← Nat.card_congr (MulAut.congr e).toEquiv,
    card_mulAut_alternating n hn hn6, Nat.card_congr e.toEquiv]

theorem normal_a7_index_dvd_two
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [S.Normal]
    (hC : Subgroup.centralizer (S : Set G) = ⊥)
    (e : alternatingGroup (Fin 7) ≃* S) : S.index ∣ 2 :=
  normal_alternating_index_dvd_two S hC 7 (by decide) (by decide) e

#print axioms GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
#print axioms card_mulAut_alternating
#print axioms normal_alternating_index_dvd_two
#print axioms normal_a7_index_dvd_two
end Conjecture55AlternatingAut
