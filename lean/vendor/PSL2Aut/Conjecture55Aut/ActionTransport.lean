module
public import Mathlib
namespace Conjecture55Aut.ActionTransport
public theorem exists_equivariant_equiv_of_stabilizer_map_eq
    {L L' X X' : Type*}
    [Group L] [MulAction L X] [MulAction.IsPretransitive L X]
    [Group L'] [MulAction L' X'] [MulAction.IsPretransitive L' X']
    (eL : L ≃* L') (a : X) (a' : X')
    (hstab : (MulAction.stabilizer L a).map eL.toMonoidHom =
      MulAction.stabilizer L' a') :
    ∃ eX : X ≃ X', ∀ l : L, ∀ x : X,
      eX (l • x) = eL l • eX x := by
  classical
  let rep : X → L := fun x =>
    Classical.choose (MulAction.exists_smul_eq L a x)
  have hrep : ∀ x : X, rep x • a = x := fun x =>
    Classical.choose_spec (MulAction.exists_smul_eq L a x)
  have hstab_iff : ∀ l : L,
      l ∈ MulAction.stabilizer L a ↔
        eL l ∈ MulAction.stabilizer L' a' := by
    intro l
    constructor
    · intro hl
      rw [← hstab, Subgroup.mem_map]
      exact ⟨l, hl, rfl⟩
    · intro hl
      rw [← hstab, Subgroup.mem_map] at hl
      rcases hl with ⟨m, hm, hml⟩
      have : m = l := eL.injective hml
      simpa [this] using hm
  have hsame_iff : ∀ l m : L,
      l • a = m • a ↔ eL l • a' = eL m • a' := by
    intro l m
    constructor
    · intro hlm
      have hfix : m⁻¹ * l ∈ MulAction.stabilizer L a := by
        change (m⁻¹ * l) • a = a
        calc
          (m⁻¹ * l) • a = m⁻¹ • (l • a) := by rw [mul_smul]
          _ = m⁻¹ • (m • a) := by rw [hlm]
          _ = a := by simp
      have hfix' := (hstab_iff (m⁻¹ * l)).1 hfix
      change eL (m⁻¹ * l) • a' = a' at hfix'
      have h := congrArg (fun x => eL m • x) hfix'
      simpa [mul_smul] using h
    · intro hlm
      have hfix' : eL (m⁻¹ * l) ∈ MulAction.stabilizer L' a' := by
        change eL (m⁻¹ * l) • a' = a'
        calc
          eL (m⁻¹ * l) • a' = (eL m)⁻¹ • (eL l • a') := by
            simp [mul_smul]
          _ = (eL m)⁻¹ • (eL m • a') := by rw [hlm]
          _ = a' := by simp
      have hfix := (hstab_iff (m⁻¹ * l)).2 hfix'
      change (m⁻¹ * l) • a = a at hfix
      have h := congrArg (fun x => m • x) hfix
      simpa [mul_smul] using h
  let pointMap : X → X' := fun x => eL (rep x) • a'
  have hpointMap_injective : Function.Injective pointMap := by
    intro x y hxy
    calc
      x = rep x • a := (hrep x).symm
      _ = rep y • a := (hsame_iff (rep x) (rep y)).2 hxy
      _ = y := hrep y
  have hpointMap_surjective : Function.Surjective pointMap := by
    intro y
    obtain ⟨l', hl'⟩ := MulAction.exists_smul_eq L' a' y
    let x : X := eL.symm l' • a
    refine ⟨x, ?_⟩
    change eL (rep x) • a' = y
    rw [← hl']
    simpa using (hsame_iff (rep x) (eL.symm l')).1 (by simp [x, hrep])
  let eX : X ≃ X' :=
    Equiv.ofBijective pointMap ⟨hpointMap_injective, hpointMap_surjective⟩
  refine ⟨eX, ?_⟩
  intro l x
  change eL (rep (l • x)) • a' = eL l • (eL (rep x) • a')
  have hsource : rep (l • x) • a = (l * rep x) • a := by
    rw [hrep, mul_smul, hrep]
  simpa [mul_smul] using
    (hsame_iff (rep (l • x)) (l * rep x)).1 hsource

end Conjecture55Aut.ActionTransport
