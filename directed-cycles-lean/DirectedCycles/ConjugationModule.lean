module

public import DirectedCycles.ElementNormalClosure
public import DirectedCycles.CocycleExtension

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- Conjugation restricted to a normal subgroup. -/
def normalConjugation {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) : N →* N where
  toFun x := ⟨g*x.val*g⁻¹, (inferInstance : N.Normal).conj_mem x.val x.property g⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; change g*(x.val*y.val)*g⁻¹ = (g*x.val*g⁻¹)*(g*y.val*g⁻¹); group

/-- The additive abelianization of a normal subgroup. -/
abbrev NormalAbelianModule {G : Type*} [Group G] (N : Subgroup G) :=
  Additive (Abelianization N)

/-- The quotient map written additively. -/
def normalAbelianElement {G : Type*} [Group G] (N : Subgroup G) (x : N) :
    NormalAbelianModule N := Additive.ofMul (Abelianization.of x)

@[simp] theorem normalAbelianElement_mul {G : Type*} [Group G] (N : Subgroup G) (x y : N) :
    normalAbelianElement N (x*y) = normalAbelianElement N x + normalAbelianElement N y :=
  congrArg Additive.ofMul (map_mul Abelianization.of x y)

@[simp] theorem normalAbelianElement_one {G : Type*} [Group G] (N : Subgroup G) :
    normalAbelianElement N 1 = 0 := rfl

@[simp] theorem normalAbelianElement_inv {G : Type*} [Group G] (N : Subgroup G) (x : N) :
    normalAbelianElement N x⁻¹ = -normalAbelianElement N x :=
  congrArg Additive.ofMul (map_inv Abelianization.of x)

theorem normalAbelianElement_surjective {G : Type*} [Group G] (N : Subgroup G) :
    Function.Surjective (normalAbelianElement N) := by
  intro x
  obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (commutator N) x.toMul
  exact ⟨y,congrArg Additive.ofMul hy⟩

/-- The integral conjugation representation on the abelianization. -/
def normalAbelianAction {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    G →* Module.End ℤ (NormalAbelianModule N) where
  toFun g := (Abelianization.map (normalConjugation N g)).toAdditive.toIntLinearMap
  map_one' := by
    ext x
    obtain ⟨b,rfl⟩ := normalAbelianElement_surjective N x
    change normalAbelianElement N (normalConjugation N 1 b) = normalAbelianElement N b
    congr 1
    apply Subtype.ext
    simp [normalConjugation]
  map_mul' g h := by
    ext x
    obtain ⟨b,rfl⟩ := normalAbelianElement_surjective N x
    change normalAbelianElement N (normalConjugation N (g*h) b) =
      normalAbelianElement N (normalConjugation N g (normalConjugation N h b))
    congr 1
    apply Subtype.ext
    simp [normalConjugation,mul_assoc]

@[simp] theorem normalAbelianAction_element {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (g : G) (b : N) :
    normalAbelianAction N g (normalAbelianElement N b) =
      normalAbelianElement N (normalConjugation N g b) := rfl

/-- Every conjugation difference is represented by the actual commutator. -/
theorem normalAbelianAction_difference {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (g : G) (b : N) :
    (normalAbelianAction N g - 1) (normalAbelianElement N b) =
      normalAbelianElement N ⟨⁅g,b.val⁆,
        N.mul_mem ((inferInstance : N.Normal).conj_mem b.val b.property g) (N.inv_mem b.property)⟩ := by
  change normalAbelianElement N (normalConjugation N g b) - normalAbelianElement N b = _
  rw [← neg_neg (normalAbelianElement N b),sub_neg_eq_add,← normalAbelianElement_inv,← normalAbelianElement_mul]
  rfl

/-- Elements of the subgroup act trivially on its abelianization. -/
theorem normalAbelianAction_internal {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (b : N) : normalAbelianAction N b.val = 1 := by
  ext x
  obtain ⟨y,rfl⟩ := normalAbelianElement_surjective N x
  change normalAbelianElement N (normalConjugation N b.val y) = normalAbelianElement N y
  have he : normalConjugation N b.val y = b*y*b⁻¹ := Subtype.ext rfl
  rw [he,normalAbelianElement_mul,normalAbelianElement_mul,normalAbelianElement_inv]
  abel

end DirectedCycles
