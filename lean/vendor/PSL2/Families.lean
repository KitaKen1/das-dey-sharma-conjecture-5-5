import CyclicSum
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
The proof of `conjugate_family_card` is adapted from the Apache-2.0-licensed
Qiuzhen-CFSG/CFSG project, commit 96b2a02085dc678f3e0a97b334c31ada599c55fd,
GorensteinWalter/Section4/SecondCasePSL2OrderPSubgroupCount.lean, lines 24–79.
The subsequent disjoint-family counting argument is new.
-/
noncomputable section
namespace CyclicSum

theorem conjugate_family_card
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) :
    Nat.card {T : Subgroup G // ∃ g : G,
      T = U.map (MulAut.conj g).toMonoidHom} =
      (Subgroup.normalizer (U : Set G)).index := by
  classical
  let : MulAction G (Subgroup G) :=
    { smul := fun g H => H.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro H
        change H.map (MulAut.conj (1 : G)).toMonoidHom = H
        apply Subgroup.ext
        intro x
        rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
          ext x; simp]
        simp
      mul_smul := by
        intro g h H
        change H.map (MulAut.conj (g * h)).toMonoidHom =
          (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have horbit :
      MulAction.orbit G U =
        {T : Subgroup G | ∃ g : G,
          T = U.map (MulAut.conj g).toMonoidHom} := by
    ext T
    constructor
    · intro hT
      rcases hT with ⟨g, rfl⟩
      exact ⟨g, by change U.map _ = _; rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, by change U.map _ = _; rfl⟩
  have hstab : MulAction.stabilizer G U =
      Subgroup.normalizer (U : Set G) := by
    ext g
    change g • U = U ↔ g ∈ Subgroup.normalizer (U : Set G)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer U),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
            MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  change Nat.card ↥{T : Subgroup G | ∃ g : G,
    T = U.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer G U, hstab]


abbrev ConjugateFamily {G : Type*} [Group G] (U : Subgroup G) :=
  {T : Subgroup G // ∃ g : G, T = U.map (MulAut.conj g).toMonoidHom}

variable {G : Type*} [Group G] [Finite G]

theorem conjugate_family_subgroup_card (U : Subgroup G) (T : ConjugateFamily U) :
    Nat.card T.1 = Nat.card U := by
  rcases T.2 with ⟨g, hg⟩
  rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]

def conjugateFamilyToCyclic (U : Subgroup G) (hU : IsCyclic U) :
    ConjugateFamily U → CyclicSubgroups G := fun T => ⟨T.1, by
  rcases T.2 with ⟨g, hg⟩
  rw [hg]
  exact (MulEquiv.isCyclic ((MulAut.conj g).subgroupMap U)).mp hU⟩

theorem cyclic_count_ge_three_families
    {p : ℕ} (U V : Subgroup G) (hU : IsCyclic U) (hV : IsCyclic V)
    (hU1 : 1 < Nat.card U) (hV1 : 1 < Nat.card V) (hp1 : 1 < p)
    (hUV : Nat.card U ≠ Nat.card V)
    (hUp : Nat.card U ≠ p) (hVp : Nat.card V ≠ p)
    (hPcard : ∀ P : Sylow p G, Nat.card P = p)
    (hPcyc : ∀ P : Sylow p G, IsCyclic P) :
    1 + (Subgroup.normalizer (U : Set G)).index +
      (Subgroup.normalizer (V : Set G)).index + Nat.card (Sylow p G) ≤
      Nat.card (CyclicSubgroups G) := by
  classical
  let fU := conjugateFamilyToCyclic U hU
  let fV := conjugateFamilyToCyclic V hV
  let fP : Sylow p G → CyclicSubgroups G := fun P => ⟨P, hPcyc P⟩
  let f0 : Unit → CyclicSubgroups G := fun _ => ⟨⊥, inferInstance⟩
  have hUi : Function.Injective fU := fun _ _ h =>
    Subtype.ext (congrArg (fun C : CyclicSubgroups G => C.val) h)
  have hVi : Function.Injective fV := fun _ _ h =>
    Subtype.ext (congrArg (fun C : CyclicSubgroups G => C.val) h)
  have hPi : Function.Injective fP := fun _ _ h =>
    Sylow.ext (congrArg Subtype.val h)
  have h0i : Function.Injective f0 := fun _ _ _ => Subsingleton.elim _ _
  have hfU (T : ConjugateFamily U) : Nat.card (fU T).1 = Nat.card U :=
    conjugate_family_subgroup_card U T
  have hfV (T : ConjugateFamily V) : Nat.card (fV T).1 = Nat.card V :=
    conjugate_family_subgroup_card V T
  have hfP (P : Sylow p G) : Nat.card (fP P).1 = p := hPcard P
  have hf0 (x : Unit) : Nat.card (f0 x).1 = 1 := Subgroup.card_bot
  have hUVne (u : ConjugateFamily U) (v : ConjugateFamily V) : fU u ≠ fV v := by
    intro heq
    have := congrArg (fun C : CyclicSubgroups G => Nat.card C.1) heq
    rw [hfU, hfV] at this
    exact hUV this
  have hUPne (u : ConjugateFamily U) (P : Sylow p G) : fU u ≠ fP P := by
    intro heq
    have := congrArg (fun C : CyclicSubgroups G => Nat.card C.1) heq
    rw [hfU, hfP] at this
    exact hUp this
  have hVPne (v : ConjugateFamily V) (P : Sylow p G) : fV v ≠ fP P := by
    intro heq
    have := congrArg (fun C : CyclicSubgroups G => Nat.card C.1) heq
    rw [hfV, hfP] at this
    exact hVp this
  have h0Une (x : Unit) (u : ConjugateFamily U) : f0 x ≠ fU u := by
    intro heq
    have := congrArg (fun C : CyclicSubgroups G => Nat.card C.1) heq
    rw [hf0 x, hfU] at this
    omega
  have h0Vne (x : Unit) (v : ConjugateFamily V) : f0 x ≠ fV v := by
    intro heq
    have := congrArg (fun C : CyclicSubgroups G => Nat.card C.1) heq
    rw [hf0 x, hfV] at this
    omega
  have h0Pne (x : Unit) (P : Sylow p G) : f0 x ≠ fP P := by
    intro heq
    have := congrArg (fun C : CyclicSubgroups G => Nat.card C.1) heq
    rw [hf0 x, hfP] at this
    omega
  have hiUV : Function.Injective (Sum.elim fU fV) := hUi.sumElim hVi hUVne
  have hiUVP : Function.Injective (Sum.elim (Sum.elim fU fV) fP) := by
    apply hiUV.sumElim hPi
    intro u P
    cases u with
    | inl u => exact hUPne u P
    | inr v => exact hVPne v P
  have hi : Function.Injective (Sum.elim f0 (Sum.elim (Sum.elim fU fV) fP)) := by
    apply h0i.sumElim hiUVP
    intro x y
    rcases y with (u | v) | P
    · exact h0Une x u
    · exact h0Vne x v
    · exact h0Pne x P
  have hcard := Nat.card_le_card_of_injective _ hi
  simpa only [Nat.card_sum, Nat.card_unique, Nat.add_assoc,
    show Nat.card (ConjugateFamily U) = (Subgroup.normalizer (U : Set G)).index from
      conjugate_family_card U,
    show Nat.card (ConjugateFamily V) = (Subgroup.normalizer (V : Set G)).index from
      conjugate_family_card V] using hcard


theorem cyclic_count_ge_psl2_families
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (U V : Subgroup G) (hU : IsCyclic U) (hV : IsCyclic V)
    (hUcard : Nat.card U = (p - 1) / 2)
    (hVcard : Nat.card V = (p + 1) / 2)
    (hUN : Nat.card (Subgroup.normalizer (U : Set G)) = 2 * Nat.card U)
    (hVN : Nat.card (Subgroup.normalizer (V : Set G)) = 2 * Nat.card V)
    (hGcard : Nat.card G = p * (p ^ 2 - 1) / 2)
    (hPcard : ∀ P : Sylow p G, Nat.card P = p)
    (hSylow : p + 1 ≤ Nat.card (Sylow p G)) :
    p ^ 2 + p + 2 ≤ Nat.card (CyclicSubgroups G) := by
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hu : 2 * Nat.card U + 1 = p := by omega
  have hv : 2 * Nat.card V = p + 1 := by omega
  have huv : Nat.card V = Nat.card U + 1 := by omega
  have hsum : Nat.card U + Nat.card V = p := by omega
  have hsq : p ^ 2 - 1 = 4 * Nat.card U * Nat.card V := by
    have heq : p ^ 2 = 4 * Nat.card U * Nat.card V + 1 := by
      rw [← hu, huv]
      ring
    omega
  have hGfact : Nat.card G = (2 * Nat.card U) * (p * Nat.card V) := by
    calc
      Nat.card G = ((2 * Nat.card U) * (p * Nat.card V) * 2) / 2 := by
        rw [hGcard, hsq]
        congr 1
        ring
      _ = _ := by simp
  have hiU : (Subgroup.normalizer (U : Set G)).index = p * Nat.card V := by
    apply Nat.eq_of_mul_eq_mul_right (m := 2 * Nat.card U) (by omega)
    have heq := (Subgroup.normalizer (U : Set G)).index_mul_card
    rw [hUN, hGfact] at heq
    simpa only [mul_comm] using heq
  have hiV : (Subgroup.normalizer (V : Set G)).index = p * Nat.card U := by
    apply Nat.eq_of_mul_eq_mul_right (m := 2 * Nat.card V) (by omega)
    have heq := (Subgroup.normalizer (V : Set G)).index_mul_card
    rw [hVN, hGfact] at heq
    convert heq using 1 <;> ring
  have hindices : (Subgroup.normalizer (U : Set G)).index +
      (Subgroup.normalizer (V : Set G)).index = p ^ 2 := by
    rw [hiU, hiV, ← Nat.mul_add]
    rw [Nat.add_comm (Nat.card V), hsum]
    ring
  let : Fact p.Prime := ⟨hp⟩
  have hPcyc (P : Sylow p G) : IsCyclic P := isCyclic_of_prime_card (hPcard P)
  have hcount := cyclic_count_ge_three_families U V hU hV
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hPcard hPcyc
  omega

#print axioms conjugate_family_card
#print axioms cyclic_count_ge_three_families
#print axioms cyclic_count_ge_psl2_families
end CyclicSum
