import Mathlib

namespace Conjecture55FrobeniusProof
open Function

theorem dvd_card_of_all_minimalPeriod_eq {X : Type*} [Fintype X]
    (f : Equiv.Perm X) (m : ℕ) (hm : ∀ x, minimalPeriod f x = m) :
    m ∣ Fintype.card X := by
  classical
  let C := Subgroup.zpowers f
  let Ω := Quotient (MulAction.orbitRel C X)
  have hc (x : X) : Fintype.card (MulAction.orbit C x) = m := by
    rw [← MulAction.minimalPeriod_eq_card f x]
    exact hm x
  rw [Fintype.card_congr (MulAction.selfEquivSigmaOrbits C X), Fintype.card_sigma]
  exact Finset.dvd_sum fun ω _ => by rw [hc]

theorem dvd_card_periodicPts_of_minimal {X : Type*} [Fintype X] [DecidableEq X]
    (f : Equiv.Perm X) {m : ℕ} (hm : 0 < m)
    (hmin : ∀ x, m ≤ minimalPeriod f x) :
    m ∣ Fintype.card {x : X // IsPeriodicPt f m x} := by
  classical
  have hi (x : X) : IsPeriodicPt f m (f x) ↔ IsPeriodicPt f m x := by
    constructor
    · intro h
      apply f.injective
      simpa only [IsPeriodicPt, IsFixedPt, Function.iterate_succ_apply,
        ← Function.iterate_succ_apply'] using h
    · exact IsPeriodicPt.apply
  let e := f.subtypePerm hi
  apply dvd_card_of_all_minimalPeriod_eq e m
  intro x
  have he : minimalPeriod e x = minimalPeriod f x.val := by
    apply minimalPeriod_eq_minimalPeriod_iff.mpr
    intro k
    have hh : ∀ y : {x : X // IsPeriodicPt f m x},
        ((e : _ → _)^[k] y).val = (f : X → X)^[k] y.val := by
      intro y
      induction k with
      | zero => rfl
      | succ k ih =>
        simpa only [Function.iterate_succ_apply', e, Equiv.Perm.subtypePerm_apply] using
          congrArg f ih
    change ((e : _ → _)^[k] x = x) ↔ _
    rw [Subtype.ext_iff, hh]
    rfl
  rw [he]
  exact Nat.le_antisymm (x.prop.minimalPeriod_le hm) (hmin x.val)

theorem exists_periodic_card_of_fixed_card_dvd {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (f : Equiv.Perm X)
    (hcard : ∀ k, (∃ x, IsPeriodicPt f k x) →
      Fintype.card {x : X // IsPeriodicPt f k x} ∣ Fintype.card X) :
    ∃ x, IsPeriodicPt f (Fintype.card X) x := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_min_image Finset.univ
    (fun x => minimalPeriod f x) Finset.univ_nonempty
  have hp : 0 < minimalPeriod f x :=
    minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts x)
  have hd := dvd_card_periodicPts_of_minimal f hp (fun y => hx y (Finset.mem_univ y))
  have he := isPeriodicPt_minimalPeriod f x
  exact ⟨x, he.trans_dvd (hd.trans (hcard _ ⟨x, he⟩))⟩

#print axioms dvd_card_periodicPts_of_minimal
#print axioms exists_periodic_card_of_fixed_card_dvd

#print axioms dvd_card_of_all_minimalPeriod_eq
end Conjecture55FrobeniusProof
