import Conjecture55Foundation

/-! The automorphisms of C16 × C2 form a 2-group; the existing normal-complement
criterion then applies when the Sylow index is squarefree. -/
namespace Conjecture55C16C2

abbrev A := ZMod 16 × ZMod 2

def e₁ : A := (1, 0)
def e₂ : A := (0, 1)

def generatorMap (a b x : A) : A := x.1.val • a + x.2.val • b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Only the images of two generators are enumerated, not all permutations. -/
theorem generatorMap_fourth :
    ∀ a b : A, (8 : ℕ) • a ≠ 0 → (2 : ℕ) • b = 0 → b ≠ 0 → b ≠ (8 : ℕ) • a →
      ∀ x : A, generatorMap a b (generatorMap a b (generatorMap a b (generatorMap a b x))) = x := by
  decide +kernel

/-- Every additive automorphism of C₁₆ × C₂ has fourth power equal to identity. -/
theorem addAut_apply_four (f : AddAut A) (x : A) : f (f (f (f x))) = x := by
  have hrep (y : A) : f y = generatorMap (f e₁) (f e₂) y := by
    have hy : y = y.1.val • e₁ + y.2.val • e₂ := by
      ext <;> simp [e₁, e₂, nsmul_eq_mul]
    calc
      f y = f (y.1.val • e₁ + y.2.val • e₂) := congrArg f hy
      _ = generatorMap (f e₁) (f e₂) y := by
        unfold generatorMap
        rw [map_add, map_nsmul, map_nsmul]
  have ha : (8 : ℕ) • f e₁ ≠ 0 := by
    have h := f.injective.ne (show (8 : ℕ) • e₁ ≠ 0 by decide)
    simpa only [map_nsmul, map_zero] using h
  have hb : (2 : ℕ) • f e₂ = 0 := by
    rw [← map_nsmul, show (2 : ℕ) • e₂ = 0 by decide, map_zero]
  have hb0 : f e₂ ≠ 0 := by
    have h := f.injective.ne (show e₂ ≠ 0 by decide)
    simpa only [map_zero] using h
  have hba : f e₂ ≠ (8 : ℕ) • f e₁ := by
    have h := f.injective.ne (show e₂ ≠ (8 : ℕ) • e₁ by decide)
    simpa only [map_nsmul] using h
  let a := f e₁
  let b := f e₂
  have hfun : (f : A → A) = generatorMap a b := funext hrep
  change (f : A → A) ((f : A → A) ((f : A → A) ((f : A → A) x))) = x
  rw [hfun]
  exact generatorMap_fourth a b ha hb hb0 hba x

/-- Multiplicative form used by the Sylow normal-complement criterion. -/
theorem mulAut_fourth (f : MulAut (Multiplicative A)) : f ^ 4 = 1 := by
  apply MulEquiv.ext
  intro x
  change f (f (f (f x))) = x
  exact addAut_apply_four (AddEquiv.toMultiplicative.symm f) x

/-- The automorphism group of C₁₆ × C₂ is a 2-group. -/
theorem isPGroup_mulAut : IsPGroup 2 (MulAut (Multiplicative A)) := by
  intro f
  exact ⟨2, by simpa using mulAut_fourth f⟩

/-- Transport the automorphism-group conclusion along a chosen group isomorphism. -/
theorem isPGroup_mulAut_of_equiv {G : Type*} [Group G]
    (e : G ≃* Multiplicative A) : IsPGroup 2 (MulAut G) :=
  isPGroup_mulAut.of_equiv (MulAut.congr e).symm

#print axioms isPGroup_mulAut_of_equiv
#print axioms mulAut_fourth
#print axioms isPGroup_mulAut
#print axioms generatorMap_fourth
#print axioms addAut_apply_four

/-- A C16 × C2 Sylow subgroup with squarefree index forces solvability. -/
theorem isSolvable_of_c16c2_sylow_of_squarefree_index
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (e : P ≃* Multiplicative A) (hs : Squarefree P.index) :
    Group.IsSolvable G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsMulCommutative P := IsMulCommutative.of_comm (fun x y => by
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _)
  exact Conjecture55Lean4Web.Conjecture55C4C2.isSolvable_of_aut_isPGroup_of_squarefree_index P
    (isPGroup_mulAut_of_equiv e) hs

#print axioms isSolvable_of_c16c2_sylow_of_squarefree_index
end Conjecture55C16C2
