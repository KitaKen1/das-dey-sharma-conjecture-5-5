module

public import GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic

namespace GorensteinWalter

private def firstFour (i : Fin 7) : Prop := i.val < 4
private instance : DecidablePred firstFour := fun _ => inferInstanceAs (Decidable (_ < 4))
private abbrev S7 := Equiv.Perm (Fin 7)
private abbrev aa : S7 := (a7a : S7)
private abbrev tt : S7 := (a7t : S7)

/- The centralizer preserves a four-point block and a three-point block.
Checking the 24 * 6 block permutations avoids enumerating the whole A7. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private theorem block_certificate :
    ∀ p : Equiv.Perm {i : Fin 7 // firstFour i},
    ∀ q : Equiv.Perm {i : Fin 7 // ¬firstFour i},
      let y := p.subtypeCongr q
      (y ≠ 1 ∧ y ^ 3 = 1 ∧ y * aa = aa * y ∧
        y ≠ aa ∧ y ≠ aa ^ 2 ∧
        ∃ i j : Fin 3, tt * y * tt⁻¹ = y ^ i.val * aa ^ j.val) → False := by
  decide +kernel

private theorem preserves_firstFour (x : S7) (hc : x * aa = aa * x) :
    ∀ i, firstFour (x i) ↔ firstFour i := by
  have hf : ∀ i : Fin 7, firstFour i ↔ aa i = i := by decide +kernel
  intro i
  rw [hf, hf]
  have h : x (aa i) = aa (x i) := congrArg (fun g : S7 => g i) hc
  constructor
  · intro hh
    exact x.injective (h.trans hh)
  · intro hh
    rw [← h, hh]

public theorem a7_no_order_nine_normalized_by_t_certificate :
    ∀ x : A7OrderThree,
      ((x : ASevenCertificateGroup) * a7a = a7a * (x : ASevenCertificateGroup) ∧
        (x : ASevenCertificateGroup) ≠ a7a ∧
        (x : ASevenCertificateGroup) ≠ a7a ^ 2 ∧
        fixedSpanThree x a7a
          (a7t * (x : ASevenCertificateGroup) * a7t⁻¹)) → False := by
  intro x ⟨hc, hxa, hxa2, i, j, hij⟩
  let y : S7 := (x.val : S7)
  have hc' : y * aa = aa * y := congrArg (fun g : ASevenCertificateGroup => (g : S7)) hc
  have hp := preserves_firstFour y hc'
  let p := y.subtypePerm hp
  let q : Equiv.Perm {i : Fin 7 // ¬firstFour i} :=
    y.subtypePerm (fun i => not_congr (hp i))
  have he : p.subtypeCongr q = y := by
    ext k
    by_cases hk : firstFour k <;> simp [p, q, Equiv.Perm.subtypeCongr.apply, hk]
  apply block_certificate p q
  rw [he]
  refine ⟨?_, ?_, hc', ?_, ?_, i, j, ?_⟩
  · intro h
    exact x.property.1 (Subtype.ext h)
  · exact congrArg (fun g : ASevenCertificateGroup => (g : S7)) x.property.2
  · intro h
    exact hxa (Subtype.ext h)
  · intro h
    exact hxa2 (Subtype.ext h)
  · exact congrArg (fun g : ASevenCertificateGroup => (g : S7)) hij

#print axioms a7_no_order_nine_normalized_by_t_certificate
end GorensteinWalter
