import ExponentShape
import RankSocle
import SylowReduction

/-! Actual structural reduction of a radical-free strict FC counterexample
using ordinary root lower bounds, with no Amiri or exact-root input. -/
namespace Conjecture55ExponentReduction
open Conjecture55Lean4Web Conjecture55Lean4Web
open Conjecture55CyclicIndex Conjecture55RankSocle Conjecture55SylowReduction
open scoped IsMulCommutative
universe u

theorem exists_simple_normal_of_strict_fc_bound
    {G : Type u} [Group G] [Fintype G] [Nontrivial G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hV4 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleGroup H → ¬IsMulCommutative H →
      ∃ E : Subgroup H, Nat.card E = 4 ∧ ∀ x : E, x ^ 2 = 1)
    {a m : ℕ} (ha : 2 ≤ a) (hm : Odd m) (P : Sylow 2 G)
    (hnc : ¬IsCyclic P) (hcard : Nat.card G = 2 ^ a * m)
    (hbase : ∀ e, e ∣ Nat.card G → e ≤ Nat.card {x : G // x ^ e = 1})
    (hlt : cyc G < 2 ^ (numPrimeFactors G + 2)) :
    ∃ S : Subgroup G, S.Normal ∧ IsSimpleGroup S ∧ ¬IsMulCommutative S ∧
      Subgroup.centralizer (S : Set G) = ⊥ := by
  by_cases ha3 : 3 ≤ a
  · obtain ⟨A, hA, hAi⟩ := RootWeights.exists_cyclic_index_two_of_strict_fc_bound
      ha3 hm P hnc hcard hbase hlt
    let : IsCyclic A := hA
    exact exists_simple_normal_centralizer_eq_bot_of_smallTwoRank hrad
      (smallTwoRank_of_sylow_cyclic_index_two P A hAi) hV4
  · have ha2 : a = 2 := by omega
    apply Conjecture55Socle.exists_simple_normal_centralizer_eq_bot hrad
    · rw [hcard]
      intro hd
      have hodd := Nat.odd_iff.mp hm
      norm_num [ha2] at hd
      omega
    · intro H _ _ hsimple hnonab
      obtain ⟨E, hE, -⟩ := hV4 H hsimple hnonab
      simpa only [hE] using E.card_subgroup_dvd_card

#print axioms exists_simple_normal_of_strict_fc_bound
end Conjecture55ExponentReduction
