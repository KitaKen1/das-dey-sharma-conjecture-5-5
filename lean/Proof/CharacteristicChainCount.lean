import CharacteristicCyclicChain
import ThreeCyclicFamilies

/-! Count characteristic cyclic chains in a Sylow subgroup of a normal
simple subgroup.  The ambient Sylow subgroup may be larger. -/

namespace Conjecture55CharacteristicCount
open Conjecture55CharacteristicChain Conjecture55ThreeFamilies
open Conjecture55Lean4Web.CyclicSum
noncomputable section

theorem count_of_characteristic_chain_in_normal_subgroup
    {G : Type*} [Group G] [Finite G] {a m : ℕ}
    (hm : Odd m) (hsf : Squarefree m) (hG : Nat.card G = 2 ^ a * m)
    (S : Subgroup G) (hSn : S.Normal) (hs : IsSimpleGroup S)
    (hn : ¬IsMulCommutative S) (h4 : 4 ∣ Nat.card S)
    (Q : Sylow 2 S) (B : Fin 3 → Subgroup Q)
    (hcyc : ∀ i, IsCyclic (B i))
    (hcard : ∀ i, Nat.card (B i) = 2 ^ (i.val + 1))
    (hchar : ∀ i, (B i).Characteristic) :
    17 * m.divisors.card ≤ 2 * Nat.card (CyclicSubgroups G) := by
  classical
  obtain ⟨P, hQP⟩ := Q.exists_comap_subtype_eq
  have hQmapP : (Q : Subgroup S).map S.subtype ≤ (P : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap, hQP]
  let fG : Q →* G := S.subtype.comp (Q : Subgroup S).subtype
  let fP : Q →* P := fG.codRestrict P (fun q => hQmapP ⟨q, q.property, rfl⟩)
  have hfP : Function.Injective fP := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P => (z : G)) hxy
  let H : Subgroup P := fP.range
  have hHmap : H.map (P : Subgroup G).subtype =
      (Q : Subgroup S).map S.subtype := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      rcases hp with ⟨q, hq⟩
      rw [← hq]
      exact ⟨q, q.property, rfl⟩
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨q, hq, rfl⟩
      let qq : Q := ⟨q, hq⟩
      refine ⟨fP qq, ⟨qq, rfl⟩, rfl⟩
  have hQmap : (Q : Subgroup S).map S.subtype = S ⊓ (P : Subgroup G) := by
    rw [← hQP, Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hH_eq : H = S.subgroupOf P := by
    apply Subgroup.map_injective (P : Subgroup G).subtype_injective
    rw [hHmap, hQmap, Subgroup.subgroupOf_map_subtype]
  have hHnormal : H.Normal := by
    rw [hH_eq]
    exact hSn.subgroupOf P
  letI : H.Normal := hHnormal
  let eQH : Q ≃* H := MonoidHom.ofInjective hfP
  let K (i : Fin 3) : Subgroup H := (B i).map eQH.toMonoidHom
  have hKchar (i : Fin 3) : (K i).Characteristic := by
    letI : (B i).Characteristic := hchar i
    exact characteristic_map_mulEquiv (B i) eQH
  let C (i : Fin 3) : Subgroup P := (K i).map H.subtype
  have hCnormal (i : Fin 3) : (C i).Normal := by
    letI : (K i).Characteristic := hKchar i
    exact inferInstance
  let A (i : Fin 3) : Subgroup G := (C i).map (P : Subgroup G).subtype
  apply seventeen_tau_le_two_cyclic_count hm hsf hG P S hs hn h4 A
  · intro i
    letI : IsCyclic (B i) := hcyc i
    have hKcyc : IsCyclic (K i) :=
      (Conjecture55Lean4Web.cyclicSubgroupMap eQH.toMonoidHom
        ⟨B i, inferInstance⟩).2
    letI : IsCyclic (K i) := hKcyc
    have hCcyc : IsCyclic (C i) :=
      (Conjecture55Lean4Web.cyclicSubgroupMap H.subtype
        ⟨K i, inferInstance⟩).2
    letI : IsCyclic (C i) := hCcyc
    exact (Conjecture55Lean4Web.cyclicSubgroupMap (P : Subgroup G).subtype
      ⟨C i, inferInstance⟩).2
  · intro i
    calc
      Nat.card (A i) = Nat.card (C i) :=
        Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective
      _ = Nat.card (K i) :=
        Subgroup.card_map_of_injective H.subtype_injective
      _ = Nat.card (B i) :=
        Subgroup.card_map_of_injective eQH.injective
      _ = 2 ^ (i.val + 1) := hcard i
  · intro i x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyH : y ∈ H := (Subgroup.map_subtype_le (K i)) hy
    rw [hH_eq] at hyH
    exact hyH
  · intro i
    letI : (C i).Normal := hCnormal i
    have h := (C i).le_normalizer_map (P : Subgroup G).subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h

#print axioms count_of_characteristic_chain_in_normal_subgroup
end
end Conjecture55CharacteristicCount
