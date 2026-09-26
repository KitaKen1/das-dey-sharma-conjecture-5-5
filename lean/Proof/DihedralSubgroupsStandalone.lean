import DihedralGeneratorsStandalone

/-! The elementary subgroup classification of finite dihedral 2-groups,
extracted from Qiuzhen/CFSG Classification.lean. It does not use the
Gorenstein-Walter classification. -/

noncomputable section
namespace Conjecture55DihedralStructure

-- (1) element case split
private lemma dihedralGroup_cases {n : ℕ} (x : DihedralGroup n) :
    (∃ i : ZMod n, x = DihedralGroup.r i) ∨ ∃ i : ZMod n, x = DihedralGroup.sr i := by
  cases hx : DihedralGroup.equivSum x with
  | inl i =>
      left
      refine ⟨i, ?_⟩
      have h1 : x = (DihedralGroup.equivSum.symm) (DihedralGroup.equivSum x) :=
        (DihedralGroup.equivSum.symm_apply_apply x).symm
      rw [hx] at h1
      simpa [DihedralGroup.equivSum] using h1
  | inr i =>
      right
      refine ⟨i, ?_⟩
      have h1 : x = (DihedralGroup.equivSum.symm) (DihedralGroup.equivSum x) :=
        (DihedralGroup.equivSum.symm_apply_apply x).symm
      rw [hx] at h1
      simpa [DihedralGroup.equivSum] using h1

-- (2) rotations lie in the rotation subgroup
private lemma r_mem_zpowers_r_one {n : ℕ} [NeZero n] (i : ZMod n) :
    DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  refine ⟨i.val, ?_⟩
  change (DihedralGroup.r 1 : DihedralGroup n) ^ i.val = DihedralGroup.r i
  rw [DihedralGroup.r_one_pow]
  congr 1
  exact ZMod.natCast_zmod_val i

-- (3) reflections are not rotations
private lemma sr_not_mem_zpowers_r_one {n : ℕ} (i : ZMod n) :
    DihedralGroup.sr i ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  intro h
  rcases (Subgroup.mem_zpowers_iff).mp h with ⟨k, hk⟩
  have hsr : DihedralGroup.sr i = DihedralGroup.r (k : ZMod n) := by
    rw [← hk, DihedralGroup.r_one_zpow]
  have h1 : DihedralGroup.sr i * (DihedralGroup.r (k : ZMod n))⁻¹ = 1 := by
    rw [hsr, mul_inv_cancel]
  have h2 : DihedralGroup.sr i * (DihedralGroup.r (k : ZMod n))⁻¹ = DihedralGroup.sr (i - (k : ZMod n)) := by
    rw [DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
    congr 1
    rw [sub_eq_add_neg]
  have h3 : DihedralGroup.sr (i - (k : ZMod n)) = 1 := by rw [← h2, h1]
  have hord : orderOf (DihedralGroup.sr (i - (k : ZMod n))) = 2 := DihedralGroup.orderOf_sr (i - (k : ZMod n))
  have hone : orderOf (1 : DihedralGroup n) = 1 := orderOf_one
  have : 2 = 1 := by rw [← hord, h3, hone]
  norm_num at this

-- (4) decomposition: H = (H ⊓ R) ∪ sr i₀ · (H ⊓ R)
private lemma mem_decomp {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m)))
    (i₀ : ZMod (2 ^ m)) (hsi : DihedralGroup.sr i₀ ∈ H)
    (x : DihedralGroup (2 ^ m)) :
    x ∈ H ↔ x ∈ H ⊓ Subgroup.zpowers (DihedralGroup.r 1) ∨
      ∃ y ∈ H ⊓ Subgroup.zpowers (DihedralGroup.r 1), x = DihedralGroup.sr i₀ * y := by
  constructor
  · intro hx
    rcases (dihedralGroup_cases x) with ⟨i, hi⟩ | ⟨i, hi⟩
    · left
      rw [hi]
      rw [hi] at hx
      exact Subgroup.mem_inf.mpr ⟨hx, r_mem_zpowers_r_one i⟩
    · right
      rw [hi]
      rw [hi] at hx
      refine ⟨DihedralGroup.r (i - i₀), ?mem, ?eq⟩
      · have h1 : DihedralGroup.r (i - i₀) ∈ H :=
          (DihedralGroup.sr_mul_sr i₀ i).symm ▸ Subgroup.mul_mem H hsi hx
        exact Subgroup.mem_inf.mpr ⟨h1, r_mem_zpowers_r_one (i - i₀)⟩
      · rw [DihedralGroup.sr_mul_r]
        congr 1
        rw [sub_eq_add_neg]
        abel
  · intro hx
    rcases hx with hx | ⟨y, hy, hyx⟩
    · exact hx.1
    · rw [hyx]
      exact Subgroup.mul_mem H hsi hy.1

-- (5) generator of H ⊓ R
private lemma generator_of_inf {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m))) :
    ∃ a : DihedralGroup (2 ^ m), a ∈ H ∧
      Subgroup.zpowers a = H ⊓ Subgroup.zpowers (DihedralGroup.r 1) := by
  let R : Subgroup (DihedralGroup (2 ^ m)) := Subgroup.zpowers (DihedralGroup.r 1)
  have hcyc : IsCyclic (↥(H ⊓ R)) := Subgroup.isCyclic_of_le inf_le_right
  rcases hcyc.exists_generator with ⟨g, hg⟩
  have hgtop : Subgroup.zpowers g = ⊤ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => hg x⟩
  let a : DihedralGroup (2 ^ m) := (g : DihedralGroup (2 ^ m))
  refine ⟨a, ?_, ?_⟩
  · change (g : DihedralGroup (2 ^ m)) ∈ H
    exact g.2.1
  · have hmap : (Subgroup.zpowers g).map (H ⊓ R).subtype = Subgroup.zpowers a := by
      simpa [a] using MonoidHom.map_zpowers (H ⊓ R).subtype g
    have htop : (⊤ : Subgroup (↥(H ⊓ R))).map (H ⊓ R).subtype = H ⊓ R := by
      ext x
      constructor
      · intro hx
        rcases (Subgroup.mem_map).mp hx with ⟨y, hy, hyx⟩
        exact hyx ▸ y.2
      · intro hx
        exact (Subgroup.mem_map).mpr ⟨⟨x, hx⟩, trivial, rfl⟩
    calc
      Subgroup.zpowers a = (Subgroup.zpowers g).map (H ⊓ R).subtype := hmap.symm
      _ = (⊤ : Subgroup (↥(H ⊓ R))).map (H ⊓ R).subtype := by rw [hgtop]
      _ = H ⊓ R := htop

-- (6) elements of a size-1 intersection are trivial
private lemma mem_eq_one_of_card_one {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m)))
    (hcard1 : Nat.card (↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = 1)
    {z : DihedralGroup (2 ^ m)} (hz : z ∈ H ⊓ Subgroup.zpowers (DihedralGroup.r 1)) : z = 1 := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  let : Fintype (↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) := Fintype.ofFinite _
  have hc1 : Fintype.card (↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = 1 := by
    rwa [Nat.card_eq_fintype_card] at hcard1
  rcases (Fintype.card_eq_one_iff).mp hc1 with ⟨z₀, hz₀⟩
  have hz' : (⟨z, hz⟩ : ↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = z₀ := hz₀ ⟨z, hz⟩
  have h1' : (⟨1, Subgroup.one_mem _⟩ : ↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = z₀ := hz₀ ⟨1, Subgroup.one_mem _⟩
  have heq : (⟨z, hz⟩ : ↥(H ⊓ Subgroup.zpowers (DihedralGroup.r 1))) = ⟨1, Subgroup.one_mem _⟩ := by
    rw [hz', h1']
  exact congrArg Subtype.val heq

-- (7) the classification
private lemma isCyclic_or_dihedral_of_subgroup_dihedral_two_group {m : ℕ} (hm : 1 ≤ m)
    (H : Subgroup (DihedralGroup (2 ^ m))) :
    IsCyclic H ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (H ≃* DihedralGroup (2 ^ k)) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  let R : Subgroup (DihedralGroup (2 ^ m)) := Subgroup.zpowers (DihedralGroup.r 1)
  by_cases hHR : H ≤ R
  · left
    exact Subgroup.isCyclic_of_le hHR
  · -- H ⊄ R
    have hx : ∃ x : DihedralGroup (2 ^ m), x ∈ H ∧ x ∉ R := by
      by_contra h
      apply hHR
      intro x hxH
      by_cases hxR : x ∈ R
      · exact hxR
      · exact False.elim (h ⟨x, hxH, hxR⟩)
    rcases hx with ⟨x, hxH, hxR⟩
    rcases (dihedralGroup_cases x) with ⟨i₀, hi₀⟩ | ⟨i₀, hi₀⟩
    · rw [hi₀] at hxR
      exact False.elim (hxR (r_mem_zpowers_r_one i₀))
    · rw [hi₀] at hxH
      rcases (generator_of_inf H) with ⟨a, ha, hgenR⟩
      have haR : a ∈ R := by
        have ha' : a ∈ H ⊓ R := by
          rw [← hgenR]
          exact Subgroup.mem_zpowers a
        exact ha'.2
      have hord : orderOf a = Nat.card (↥(H ⊓ R)) := by
        calc
          orderOf a = Fintype.card (↥(Subgroup.zpowers a)) := (Fintype.card_zpowers (x := a)).symm
          _ = Nat.card (↥(Subgroup.zpowers a)) := Nat.card_eq_fintype_card.symm
          _ = Nat.card (↥(H ⊓ R)) := by rw [hgenR]
      have hRcard : Nat.card (↥R) = 2 ^ m := by
        calc
          Nat.card (↥R) = Fintype.card (↥R) := Nat.card_eq_fintype_card
          _ = orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) := Fintype.card_zpowers (x := DihedralGroup.r 1)
          _ = 2 ^ m := DihedralGroup.orderOf_r_one
      have hdiv : Nat.card (↥(H ⊓ R)) ∣ 2 ^ m := by
        have hle : Nat.card (↥(H ⊓ R)) ∣ Nat.card (↥R) := Subgroup.card_dvd_of_le inf_le_right
        rwa [hRcard] at hle
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdiv with ⟨k, hkle, hkpow⟩
      by_cases hcard1 : Nat.card (↥(H ⊓ R)) = 1
      · left
        refine Subgroup.isCyclic_of_le (H := H) (H' := Subgroup.zpowers (DihedralGroup.sr i₀)) ?_
        intro x hx
        rcases (mem_decomp H i₀ hxH x).mp hx with h1 | ⟨y, hy, hyx⟩
        · -- x ∈ H ⊓ R of size 1: x = 1
          have hx1 : x = 1 := mem_eq_one_of_card_one H hcard1 h1
          exact hx1 ▸ Subgroup.one_mem (Subgroup.zpowers (DihedralGroup.sr i₀))
        · -- x = sr i₀ · y with y ∈ H ⊓ R of size 1: y = 1
          have hy1 : y = 1 := mem_eq_one_of_card_one H hcard1 hy
          rw [hyx, hy1, mul_one]
          exact Subgroup.mem_zpowers (DihedralGroup.sr i₀)
      · -- |H ⊓ R| ≥ 2: apply the core
        have hrelD : DihedralGroup.sr i₀ * a * (DihedralGroup.sr i₀)⁻¹ = a⁻¹ := by
          rcases (Subgroup.mem_zpowers_iff).mp haR with ⟨t, ht⟩
          have hat : a = DihedralGroup.r (t : ZMod (2 ^ m)) := by
            rw [← ht, DihedralGroup.r_one_zpow]
          calc
            DihedralGroup.sr i₀ * a * (DihedralGroup.sr i₀)⁻¹ =
                DihedralGroup.sr i₀ * DihedralGroup.r (t : ZMod (2 ^ m)) * (DihedralGroup.sr i₀)⁻¹ := by rw [hat]
            _ = DihedralGroup.sr (i₀ + (t : ZMod (2 ^ m))) * (DihedralGroup.sr i₀)⁻¹ := by rw [DihedralGroup.sr_mul_r]
            _ = DihedralGroup.sr (i₀ + (t : ZMod (2 ^ m))) * DihedralGroup.sr i₀ := by rw [DihedralGroup.inv_sr]
            _ = DihedralGroup.r (i₀ - (i₀ + (t : ZMod (2 ^ m)))) := by rw [DihedralGroup.sr_mul_sr]
            _ = DihedralGroup.r (-(t : ZMod (2 ^ m))) := by congr 1; abel
            _ = (DihedralGroup.r (t : ZMod (2 ^ m)))⁻¹ := by rw [DihedralGroup.inv_r]
            _ = a⁻¹ := by rw [hat]
        have hrel' : (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H) * ⟨a, ha⟩ * (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H)⁻¹ = (⟨a, ha⟩ : ↥H)⁻¹ := by
          apply Subtype.ext
          simpa [Subtype.ext_iff] using hrelD
        have hσ2' : (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H) ^ 2 = 1 := by
          apply Subtype.ext
          simpa [Subtype.ext_iff, pow_two] using (DihedralGroup.sr_mul_self i₀)
        have hgen : ⊤ = Subgroup.zpowers (⟨a, ha⟩ : ↥H) ⊔ Subgroup.zpowers (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H) := by
          have hHjoin : H = Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀) := by
            apply le_antisymm
            · intro x hx
              rcases (mem_decomp H i₀ hxH x).mp hx with h1 | ⟨y, hy, hyx⟩
              · exact (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀)) (by rwa [← hgenR] at h1)
              · rw [hyx]
                exact Subgroup.mul_mem (Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀))
                  ((le_sup_right : Subgroup.zpowers (DihedralGroup.sr i₀) ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀)) (Subgroup.mem_zpowers (DihedralGroup.sr i₀)))
                  ((le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers (DihedralGroup.sr i₀)) (by rwa [← hgenR] at hy))
            · exact sup_le ((Subgroup.zpowers_le).mpr ha) ((Subgroup.zpowers_le).mpr hxH)
          apply le_antisymm
          · intro x hx
            have hx1 : (x : DihedralGroup (2 ^ m)) ∈
                (Subgroup.zpowers (⟨a, ha⟩ : ↥H) ⊔ Subgroup.zpowers (⟨DihedralGroup.sr i₀, hxH⟩ : ↥H)).map H.subtype := by
              simpa [Subgroup.map_sup, MonoidHom.map_zpowers, hHjoin] using x.2
            rcases (Subgroup.mem_map).mp hx1 with ⟨y, hy, hyx⟩
            have hyx' : y = x := Subtype.ext hyx
            exact hyx' ▸ hy
          · intro x hx
            trivial
        rcases (isCyclic_or_dihedral_of_generators (D := ↥H)
          (ρ := ⟨a, ha⟩) (σ := ⟨DihedralGroup.sr i₀, hxH⟩) hgen hσ2' hrel') with hcyc | hdih
        · left
          exact hcyc
        · right
          have hk1 : 1 ≤ k := by
            have hpos : 0 < Nat.card (↥(H ⊓ R)) := Nat.card_pos
            have h2 : 2 ≤ Nat.card (↥(H ⊓ R)) := by omega
            rw [hkpow] at h2
            have hk0 : k ≠ 0 := by
              intro hk0
              rw [hk0] at h2
              norm_num at h2
            omega
          refine ⟨k, hk1, ?_⟩
          have hord' : orderOf (⟨a, ha⟩ : ↥H) = orderOf a := by
            exact (orderOf_injective H.subtype (Subtype.coe_injective) ⟨a, ha⟩).symm
          rw [hord', hord, hkpow] at hdih
          exact hdih

/-! Public interface for the dihedral-subgroup classification used by the
    Gorenstein--Walter Proposition-9 translation. -/

theorem subgroups_dihedral_twoGroup_cyclic_or_dihedral {m : ℕ} (hm : 1 ≤ m)
    (H : Subgroup (DihedralGroup (2 ^ m))) :
    IsCyclic H ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (H ≃* DihedralGroup (2 ^ k)) := by
  exact isCyclic_or_dihedral_of_subgroup_dihedral_two_group hm H


end Conjecture55DihedralStructure

#print axioms Conjecture55DihedralStructure.subgroups_dihedral_twoGroup_cyclic_or_dihedral
