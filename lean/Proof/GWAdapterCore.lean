import GorensteinWalter.Classification
import GorensteinWalter.LinearThreeEquiv
import GorensteinWalter.PSL2PerfectSubnormal
import StructuralAssembly

/-! The small-dihedral assembly boundary follows from the literal GW classification.
The GW proof itself is supplied only by the separate final endpoint wrapper. -/
namespace Conjecture55GWAdapter
open GorensteinWalter
open scoped Pointwise

universe u

lemma isPerfect_of_simple_noncommutative
    (G : Type u) [Group G] (hs : IsSimpleGroup G) (hn : ¬IsMulCommutative G) :
    Group.IsPerfect G := by
  apply Group.isPerfect_def.mpr
  exact (hs.eq_bot_or_eq_top_of_normal (commutator G) inferInstance).resolve_left
    (fun h => hn ((commutator_eq_bot_iff G).mp h))

lemma two_dvd_card_of_small_dihedral_sylow
    {G : Type u} [Group G] [Finite G] (P : Sylow 2 G)
    (hP : Nonempty (P ≃* DihedralGroup 2) ∨ Nonempty (P ≃* DihedralGroup 4)) :
    2 ∣ Nat.card G := by
  have hP2 : 2 ∣ Nat.card P := by
    rcases hP with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      norm_num
    · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      norm_num
  exact hP2.trans (P : Subgroup G).card_subgroup_dvd_card

lemma hasDihedralSylowTwo_of_small_dihedral_sylow
    {G : Type u} [Group G] [Finite G] (P : Sylow 2 G)
    (hP : Nonempty (P ≃* DihedralGroup 2) ∨ Nonempty (P ≃* DihedralGroup 4)) :
    HasDihedralSylowTwo G := by
  intro Q
  rcases hP with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ⟨1, by omega, ⟨(Sylow.equiv Q P).trans e⟩⟩
  · exact ⟨2, by omega, ⟨(Sylow.equiv Q P).trans e⟩⟩

lemma pPrimeCore_two_eq_bot_of_simple_even
    {G : Type u} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (h2 : 2 ∣ Nat.card G) :
    pPrimeCore 2 G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (pPrimeCore 2 G)
    (pPrimeCore_normal (p := 2) (G := G)) with h | h
  · exact h
  · have hc := pPrimeCore_coprime_card (p := 2) (G := G)
    rw [h, Subgroup.card_top] at hc
    exact False.elim (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) (dvd_refl 2) h2 hc)

lemma normal_odd_index_eq_top_of_simple_even
    {G : Type u} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (h2 : 2 ∣ Nat.card G)
    (L : Subgroup G) (hLn : L.Normal) (hLi : Odd L.index) : L = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal L hLn with h | h
  · rw [h, Subgroup.index_bot] at hLi
    exact False.elim (hLi.not_two_dvd_nat h2)
  · exact h

lemma not_simple_pgl2_odd
    (K : Type u) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    ¬ IsSimpleGroup (PGL2 K) := by
  intro hs
  obtain ⟨hb, ht⟩ := pgl2_commutator_ne_bot_ne_top K hK
  exact (hs.eq_bot_or_eq_top_of_normal (commutator (PGL2 K)) inferInstance).elim hb ht

lemma field_card_gt_three_of_psl2_simple_noncommutative
    {G : Type u} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ¬IsMulCommutative G)
    (K : Type u) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (e : G ≃* PSL2 K) : 3 < Nat.card K := by
  let : Group.IsPerfect G := isPerfect_of_simple_noncommutative G hs hn
  let : Group.IsPerfect (PSL2 K) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Nontrivial G := hs.toNontrivial
  let : Nontrivial (PSL2 K) := e.symm.surjective.nontrivial
  exact (psl2_perfect_subnormal_eq_top K hK ⊤ top_ne_bot inferInstance
    (Subgroup.Normal.isSubnormal inferInstance)).1

lemma exists_galoisField_model
    {G : Type u} [Group G] [Finite G]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hlarge : 3 < Nat.card K)
    (e : G ≃* PSL2 K) :
    ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ f ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) := by
  classical
  obtain ⟨p, f, hp, hpodd, hf, hcard⟩ := hK
  let : Fact p.Prime := ⟨hp⟩
  have hf0 : f ≠ 0 := by omega
  have hodd : Odd (p ^ f) := hpodd.pow
  have hlarge' : 5 ≤ p ^ f := by
    rw [hcard] at hlarge
    have := Nat.odd_iff.mp hodd
    omega
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (GaloisField p f) := Fintype.ofFinite _
  let eK : K ≃+* GaloisField p f := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card p f hf0, hcard])
  exact ⟨p, f, inferInstance, hpodd, hlarge', ⟨e.trans (psl2RingEquiv eK)⟩⟩

/-- A nonabelian simple even D-group has one of the exact models needed by the assembly. -/
theorem simple_model_of_isDGroup
    (G : Type u) [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ¬IsMulCommutative G)
    (h2 : 2 ∣ Nat.card G) (hDG : IsDGroup G) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ f ∧
        Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) := by
  classical
  have hcore := pPrimeCore_two_eq_bot_of_simple_even hs h2
  let Q := G ⧸ pPrimeCore 2 G
  let eQ : Q ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hsQ : IsSimpleGroup Q := (MulEquiv.isSimpleGroup_congr eQ).mpr hs
  have h2Q : 2 ∣ Nat.card Q := by rw [Nat.card_congr eQ.toEquiv]; exact h2
  rcases hDG with ⟨_, htwo⟩ | ⟨_, e7⟩ | ⟨_, K, hK, L, hLn, hLi, hmodel⟩
  · let : IsSimpleGroup G := hs
    let : Nontrivial Q := eQ.surjective.nontrivial
    let : Group.IsPerfect G := isPerfect_of_simple_noncommutative G hs hn
    let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (f := eQ.symm.toMonoidHom) eQ.symm.surjective
    exact False.elim (Group.IsPerfect.not_isNilpotent Q htwo.isNilpotent)
  · exact Or.inl ⟨eQ.symm.trans e7.some⟩
  · have hLtop : L = ⊤ := normal_odd_index_eq_top_of_simple_even hsQ h2Q L hLn hLi
    let eL : L ≃* Q := (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
    let eGL : G ≃* L := eQ.symm.trans eL.symm
    rcases hmodel with ⟨⟨ePSL⟩⟩ | ⟨⟨ePGL⟩⟩
    · let eG : G ≃* PSL2 K := eGL.trans ePSL
      exact Or.inr (exists_galoisField_model K hK
        (field_card_gt_three_of_psl2_simple_noncommutative hs hn K hK eG) eG)
    · have hsPGL : IsSimpleGroup (PGL2 K) :=
        (MulEquiv.isSimpleGroup_congr (eGL.trans ePGL)).mp hs
      exact False.elim (not_simple_pgl2_odd K hK hsPGL)

/-- The exact assembly input follows from the literal GW statement. -/
theorem simpleDihedralInput_of_gorensteinWalterStatement
    (hGW : GorensteinWalter.gorensteinWalterStatement.{0}) :
    Conjecture55Assembly.SimpleDihedralInput := by
  intro S _ _ hs hn P hP
  exact simple_model_of_isDGroup S hs hn
    (two_dvd_card_of_small_dihedral_sylow P hP)
    (hGW S (hasDihedralSylowTwo_of_small_dihedral_sylow P hP))

/-- The same literal classification supplies arbitrary dihedral Sylow order,
as required by the direct exponent route with two-parts up to 32. -/
theorem simple_model_of_dihedral_sylow_of_statement
    (hGW : GorensteinWalter.gorensteinWalterStatement.{u})
    (G : Type u) [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ¬IsMulCommutative G)
    {l : ℕ} (hl : 1 ≤ l) (P : Sylow 2 G)
    (e : P ≃* DihedralGroup (2 ^ l)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ f ∧
        Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) := by
  have h2P : 2 ∣ Nat.card P := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    exact dvd_mul_right _ _
  have h2 : 2 ∣ Nat.card G := h2P.trans (P : Subgroup G).card_subgroup_dvd_card
  have hD : HasDihedralSylowTwo G := by
    intro Q
    exact ⟨l, hl, ⟨(Sylow.equiv Q P).trans e⟩⟩
  exact simple_model_of_isDGroup G hs hn h2 (hGW G hD)

#print axioms simple_model_of_dihedral_sylow_of_statement
#print axioms isPerfect_of_simple_noncommutative
#print axioms two_dvd_card_of_small_dihedral_sylow
#print axioms hasDihedralSylowTwo_of_small_dihedral_sylow
#print axioms pPrimeCore_two_eq_bot_of_simple_even
#print axioms normal_odd_index_eq_top_of_simple_even
#print axioms not_simple_pgl2_odd
#print axioms field_card_gt_three_of_psl2_simple_noncommutative
#print axioms exists_galoisField_model
#print axioms simple_model_of_isDGroup
#print axioms simpleDihedralInput_of_gorensteinWalterStatement
end Conjecture55GWAdapter
