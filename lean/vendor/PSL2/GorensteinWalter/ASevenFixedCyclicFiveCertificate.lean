module

public import GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic

namespace GorensteinWalter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
public theorem a7_fixed_cyclic_five_certificate :
    ∀ x : ASevenCertificateGroup,
      (x ≠ 1 ∧ x ^ 5 = 1 ∧
        fixedSpanPow 5 x (a7a * x * a7a⁻¹)) →
      a7t * x = x * a7t := by
  intro x ⟨hx, hx5, i, hi⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ho : orderOf x = 5 := orderOf_eq_prime hx5 hx
  let F : MulAut ASevenCertificateGroup := MulAut.conj a7a
  have hF : F x = x ^ i.val := hi
  have hF3 : F ^ 3 = 1 := by
    change (MulAut.conj a7a) ^ 3 = 1
    rw [← map_pow, show a7a ^ 3 = 1 by decide +kernel, map_one]
  have he : x ^ (i.val ^ 3) = x := by
    calc
      x ^ (i.val ^ 3) = F (F (F x)) := by
        rw [hF, map_pow, hF, map_pow, map_pow, hF]
        simp only [← pow_mul]
        congr 1
        ring
      _ = (F ^ 3) x := rfl
      _ = x := by rw [hF3]; rfl
  have hi1 : i.val = 1 := by
    have he' : x ^ (i.val ^ 3) = x ^ 1 := by simpa using he
    have hm := pow_inj_mod.mp he'
    rw [ho] at hm
    fin_cases i <;> norm_num at *
  have hax : a7a * x = x * a7a := by
    have hh : a7a * x * a7a⁻¹ = x := by simpa [hi1, F, MulAut.conj_apply] using hF
    exact (mul_inv_eq_iff_eq_mul).mp hh
  let a : Equiv.Perm (Fin 7) := a7a
  let C : Subgroup (Equiv.Perm (Fin 7)) := Subgroup.centralizer ({a} : Set _)
  have hxC : (x : Equiv.Perm (Fin 7)) ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = a := Set.mem_singleton_iff.mp hy
    subst y
    exact congrArg Subtype.val hax
  let z : C := ⟨x, hxC⟩
  have hz5 : z ^ 5 = 1 := by
    apply Subtype.ext
    exact congrArg (fun w : ASevenCertificateGroup => (w : Equiv.Perm (Fin 7))) hx5
  have hz : z ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    exact congrArg (fun w : C => (w : Equiv.Perm (Fin 7))) h
  have horder : orderOf z = 5 := orderOf_eq_prime hz5 hz
  have hd := orderOf_dvd_natCard z
  have htype : a.cycleType = {3} := by decide +kernel
  have hcard : Nat.card C = 72 := by
    rw [Equiv.Perm.nat_card_centralizer, htype]
    norm_num
  rw [horder, hcard] at hd
  norm_num at hd


#print axioms a7_fixed_cyclic_five_certificate
end GorensteinWalter
