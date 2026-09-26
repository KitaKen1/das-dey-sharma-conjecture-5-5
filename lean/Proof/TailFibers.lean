import TailCore

noncomputable section
namespace Conjecture55FrobeniusProof
open Function
variable {G : Type*} [Group G]

abbrev Roots (G : Type*) [Group G] (n : ℕ) := {x : G // x ^ n = 1}
def RootTails (H : Subgroup G) (n : ℕ) := Set.range (fun x : Roots G n => powerTail H x.val)
def rootTailMap (H : Subgroup G) (n : ℕ) (x : Roots G n) : RootTails H n :=
  ⟨powerTail H x.val, ⟨x, rfl⟩⟩

instance rootTailsMulAction (H : Subgroup G) (n : ℕ) : MulAction H (RootTails H n) where
  smul h t := ⟨h • t.val, by
    obtain ⟨x, hx⟩ := t.prop
    let y : Roots G n := ⟨(h : G) * x.val * (h : G)⁻¹, by
      rw [conj_pow, x.prop]; simp⟩
    refine ⟨y, ?_⟩
    change powerTail H ((h : G) * x.val * (h : G)⁻¹) = h • t.val
    rw [tail_conj]
    exact congrArg (fun z => h • z) hx⟩
  one_smul t := Subtype.ext (one_smul H t.val)
  mul_smul h₁ h₂ t := Subtype.ext (mul_smul h₁ h₂ t.val)

def coreStabilizerEquiv (H : Subgroup G) (n : ℕ) (x : Roots G n) :
    powerCore H x.val ≃ MulAction.stabilizer H (rootTailMap H n x) where
  toFun u := ⟨⟨u.val, powerCore_le H x.val u.prop⟩, by
    apply Subtype.ext
    funext k
    change (↑(u.val * x.val ^ k) : G ⧸ H) = ↑(x.val ^ k)
    symm
    apply QuotientGroup.eq.mpr
    simpa only [mul_assoc] using u.prop k⟩
  invFun h := ⟨h.val.val, by
    intro k
    have ht := congrArg (fun t : RootTails H n => t.val k) h.prop
    change (↑(h.val.val * x.val ^ k) : G ⧸ H) = ↑(x.val ^ k) at ht
    simpa only [mul_assoc] using QuotientGroup.eq.mp ht.symm⟩
  left_inv u := by apply Subtype.ext; rfl
  right_inv h := by apply Subtype.ext; apply Subtype.ext; rfl

def rootFiberCoreEquiv [Finite G] (H : Subgroup G) (n : ℕ)
    (hn : Nat.card H ∣ n) (x : Roots G n) :
    {y : Roots G n // powerTail H y.val = powerTail H x.val} ≃ powerCore H x.val where
  toFun y := ⟨x.val⁻¹ * y.val.val, (tail_eq_iff_core H x.val y.val.val).mp y.prop.symm⟩
  invFun u := ⟨⟨x.val * u.val,
    pow_mul_eq_one_of_mem_normalizer (powerCore H x.val)
      ((Subgroup.card_dvd_of_le (powerCore_le H x.val)).trans hn)
      x.val x.prop (mem_normalizer_powerCore H x.val) u⟩,
    tail_mul_core H x.val u⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv u := by apply Subtype.ext; simp

def rootTailFiberEquiv [Finite G] (H : Subgroup G) (n : ℕ)
    (hn : Nat.card H ∣ n) (t : RootTails H n) :
    {x : Roots G n // rootTailMap H n x = t} ≃ MulAction.stabilizer H t := by
  let x := Classical.choose t.prop
  have hx := Classical.choose_spec t.prop
  have he : rootTailMap H n x = t := Subtype.ext hx
  have E : {y : Roots G n // rootTailMap H n y = rootTailMap H n x} ≃
      MulAction.stabilizer H (rootTailMap H n x) :=
    (Equiv.subtypeEquivRight (fun y => Subtype.ext_iff)).trans
      ((rootFiberCoreEquiv H n hn x).trans (coreStabilizerEquiv H n x))
  exact he ▸ E

theorem subgroup_card_dvd_root_card [Finite G] (H : Subgroup G) (n : ℕ)
    (hn : Nat.card H ∣ n) : Nat.card H ∣ Nat.card (Roots G n) := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite H
  letI : Fintype (Roots G n) := inferInstanceAs (Fintype {x : G // x ^ n = 1})
  letI : Finite (RootTails H n) := inferInstanceAs
    (Finite (Set.range (fun x : Roots G n => powerTail H x.val)))
  letI := Fintype.ofFinite (RootTails H n)
  simpa only [Nat.card_eq_fintype_card] using
    group_card_dvd_card_of_fiber_equiv_stabilizer (H := H)
      (rootTailMap H n) (rootTailFiberEquiv H n hn)

#print axioms coreStabilizerEquiv
#print axioms rootFiberCoreEquiv
#print axioms rootTailFiberEquiv
#print axioms subgroup_card_dvd_root_card
end Conjecture55FrobeniusProof
