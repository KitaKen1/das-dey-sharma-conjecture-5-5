import NormalCyclicChain
import ThreeCyclicFamilies
import ExponentBounds

/-! Transport a normal cyclic chain in a full two-subgroup to the ambient group. -/
namespace Conjecture55EmbeddedChain
open Conjecture55ThreeFamilies Conjecture55Lean4Web.CyclicSum
noncomputable section
variable {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]

theorem count_of_embedded_chain {a m : ℕ} (hm : Odd m) (hsf : Squarefree m)
    (hG : Nat.card G = 2 ^ a * m) (hQ : Nat.card Q = 2 ^ a)
    (S : Subgroup G) (hs : IsSimpleGroup S) (hn : ¬IsMulCommutative S)
    (h4 : 4 ∣ Nat.card S) (f : Q →* G) (hf : Function.Injective f)
    (hfS : f.range ≤ S) (B : Fin 3 → Subgroup Q)
    (hcyc : ∀ i, IsCyclic (B i)) (hcard : ∀ i, Nat.card (B i) = 2 ^ (i.val + 1))
    (hnorm : ∀ i, (B i).Normal) :
    17 * m.divisors.card ≤ 2 * Nat.card (CyclicSubgroups G) := by
  classical
  let R := f.range
  have hRc : Nat.card R = 2 ^ a :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm).trans hQ
  obtain ⟨P, hRP⟩ := (IsPGroup.of_card hRc).exists_le_sylow
  have hPeq : (P : Subgroup G) = R := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hRP
    exact le_of_eq ((RootWeights.sylow_card_eq_two_part P hm hG).trans hRc.symm)
  let A (i : Fin 3) := (B i).map f
  apply seventeen_tau_le_two_cyclic_count hm hsf hG P S hs hn h4 A
  · intro i
    exact (Conjecture55Lean4Web.cyclicSubgroupMap f ⟨B i, hcyc i⟩).2
  · intro i
    exact (Subgroup.card_map_of_injective hf).trans (hcard i)
  · intro i
    exact (Subgroup.map_le_range f (B i)).trans hfS
  · intro i
    let : (B i).Normal := hnorm i
    rw [hPeq]
    have h := (B i).le_normalizer_map f
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] at h

#print axioms count_of_embedded_chain
end
end Conjecture55EmbeddedChain
