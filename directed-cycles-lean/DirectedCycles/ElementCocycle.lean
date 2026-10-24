import DirectedCycles.ConjugationModule

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- The commutator map into the additive abelianization of [G,a]. -/
def elementCocycle {G : Type*} [Group G] (a g : G) :
    NormalAbelianModule (elementCommutators a) :=
  normalAbelianElement (elementCommutators a) ⟨⁅g,a⁆,mem_elementCommutators a g⟩

/-- The manuscript's commutator cocycle identity, for the actual action. -/
theorem elementCocycle_identity {G : Type*} [Group G] (a : G) :
    IsAdditiveCocycle (normalAbelianAction (elementCommutators a)) (elementCocycle a) := by
  intro g h
  let b : elementCommutators a := ⟨⁅g,a⁆,mem_elementCommutators a g⟩
  let d : elementCommutators a := ⟨⁅h,a⁆,mem_elementCommutators a h⟩
  have he : (⟨⁅g*h,a⁆,mem_elementCommutators a (g*h)⟩ : elementCommutators a) =
      normalConjugation (elementCommutators a) g d * b := by
    apply Subtype.ext
    change ⁅g*h,a⁆ = g*⁅h,a⁆*g⁻¹*⁅g,a⁆
    simp only [commutatorElement_def]
    group
  change normalAbelianElement _ _ = normalAbelianElement _ b +
    normalAbelianAction _ g (normalAbelianElement _ d)
  rw [he,normalAbelianElement_mul,normalAbelianAction_element,add_comm]

/-- Conjugation by a commutes with every ambient conjugation on B/B'. -/
theorem elementCocycle_action_commute {G : Type*} [Group G] (a g : G) :
    Commute (normalAbelianAction (elementCommutators a) g)
      (normalAbelianAction (elementCommutators a) a) := by
  let T := normalAbelianAction (elementCommutators a)
  have he : g*a = ⁅g,a⁆*a*g := by simp only [commutatorElement_def]; group
  change T g * T a = T a * T g
  rw [← map_mul,he,map_mul,map_mul,
    normalAbelianAction_internal (elementCommutators a) ⟨⁅g,a⁆,mem_elementCommutators a g⟩,one_mul]

@[simp] theorem elementCocycle_self {G : Type*} [Group G] (a : G) :
    elementCocycle a a = 0 := by
  change normalAbelianElement _ _ = _
  have he : (⟨⁅a,a⁆,mem_elementCommutators a a⟩ : elementCommutators a) = 1 :=
    Subtype.ext (by simp)
  rw [he,normalAbelianElement_one]

/-- On B the cocycle equals I-L. -/
theorem elementCocycle_internal {G : Type*} [Group G] (a : G) (b : elementCommutators a) :
    elementCocycle a b.val = normalAbelianElement _ b -
      normalAbelianAction (elementCommutators a) a (normalAbelianElement _ b) := by
  have he : (⟨⁅b.val,a⁆,mem_elementCommutators a b.val⟩ : elementCommutators a) =
      b*(normalConjugation (elementCommutators a) a b)⁻¹ := by
    apply Subtype.ext
    change ⁅b.val,a⁆ = b.val*(a*b.val*a⁻¹)⁻¹
    simp only [commutatorElement_def]
    group
  change normalAbelianElement _ _ = _
  rw [he,normalAbelianElement_mul,normalAbelianElement_inv,normalAbelianAction_element,sub_eq_add_neg]

end DirectedCycles
