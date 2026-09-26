import FrobeniusBridge

/-! Genuine root-count descent, using only ordinary Frobenius divisibility. -/
namespace Conjecture55AmiriBypass
open Conjecture55Frobenius
universe u

theorem exact_root_count_halves
    (hdiv : RootDivisibilityInput.{u})
    {G : Type u} [Group G] [Finite G] (n : ℕ)
    (hbig : 4 * n ∣ Nat.card G)
    (heq : Nat.card {x : G // x ^ (2 * n) = 1} = 2 * n) :
    Nat.card {x : G // x ^ n = 1} = n := by
  have hn : 0 < n := by
    have := Nat.pos_of_dvd_of_pos hbig (Nat.card_pos (α := G))
    omega
  have hsmall : n ∣ Nat.card G := (show n ∣ 4 * n from ⟨4, by omega⟩).trans hbig
  let f : {x : G // x ^ n = 1} → {x : G // x ^ (2 * n) = 1} :=
    fun x => ⟨x.1, by rw [mul_comm 2 n, pow_mul, x.2, one_pow]⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {x : G // x ^ (2 * n) = 1} => z.1) h)
  have hlt : Nat.card {x : G // x ^ n = 1} < 2 * n := by
    by_contra h
    have hs : Function.Surjective f :=
      (hf.bijective_of_nat_card_le (by rw [heq]; omega)).2
    have hroot : ∀ x : G, x ^ (2 * n) = 1 → x ^ n = 1 := by
      intro x hx
      obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
      have hyx : y.1 = x := congrArg Subtype.val hy
      exact hyx ▸ y.2
    let g : {x : G // x ^ (4 * n) = 1} → {x : G // x ^ (2 * n) = 1} :=
      fun x => ⟨x.1, by
        have hsq : (x.1 ^ 2) ^ (2 * n) = 1 := by
          rw [← pow_mul, show 2 * (2 * n) = 4 * n by omega]
          exact x.2
        simpa only [← pow_mul] using hroot (x.1 ^ 2) hsq⟩
    have hg : Function.Injective g := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : {x : G // x ^ (2 * n) = 1} => z.1) h)
    have hle := Nat.card_le_card_of_injective g hg
    have hlo := root_lower_bound_of_divisibility hdiv (G := G) (4 * n) hbig
    rw [heq] at hle
    omega
  obtain ⟨k, hk⟩ := hdiv G n hsmall
  have hlo := root_lower_bound_of_divisibility hdiv (G := G) n hsmall
  have hk1 : k = 1 := by nlinarith
  simpa [hk1] using hk

#print axioms exact_root_count_halves

/-- Equality of root counts descends through the entire 2-part. No parity
assumption on d and no subgroup-closure theorem are used. -/
theorem exact_root_count_descends_two_part
    (hdiv : RootDivisibilityInput.{u})
    {G : Type u} [Group G] [Finite G] (j d : ℕ)
    (hbig : 2 ^ (j + 1) * d ∣ Nat.card G)
    (heq : Nat.card {x : G // x ^ (2 ^ j * d) = 1} = 2 ^ j * d) :
    Nat.card {x : G // x ^ d = 1} = d := by
  revert hbig heq
  induction j with
  | zero =>
    intro _ heq
    simpa using heq
  | succ j ih =>
    intro hbig heq
    have h4 : 4 * (2 ^ j * d) ∣ Nat.card G := by
      have he : 4 * (2 ^ j * d) = 2 ^ (j + 1 + 1) * d := by
        rw [pow_succ, pow_succ]
        ring
      rw [he]
      exact hbig
    have he2 : Nat.card {x : G // x ^ (2 * (2 ^ j * d)) = 1} =
        2 * (2 ^ j * d) := by
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using heq
    have hhalf := exact_root_count_halves hdiv (G := G) (2 ^ j * d) h4 he2
    apply ih ?_ hhalf
    exact (mul_dvd_mul (pow_dvd_pow 2 (by omega : j + 1 ≤ j + 1 + 1))
      (dvd_refl d)).trans hbig

#print axioms exact_root_count_descends_two_part
end Conjecture55AmiriBypass
