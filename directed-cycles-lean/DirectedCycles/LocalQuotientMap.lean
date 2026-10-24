import DirectedCycles.LocalQuotientHom
import DirectedCycles.LocalQuotientSeparation

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G H : Type*} [Group G] [Group H]
    {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)
    {Q U T : Set H} (hQ : LocalNormalSet Q U)
    (hT1 : (1 : H) ∈ T) (hTi : T⁻¹ = T) (hT6 : T^6 ⊆ U)
    (f : G →* H) (hPQ : ∀ x ∈ P, f x ∈ Q) (hWT : ∀ x ∈ W, f x ∈ T)

/-- The actual map of window quotients induced by an ambient homomorphism.
The relation is tested in P and Q themselves, not their generated subgroups. -/
def quotientMap : hP.WindowQuotient hW1 hWi hW6 → hQ.WindowQuotient hT1 hTi hT6 :=
  Quotient.map (fun a : W => (⟨f a.val,hWT a.val a.property⟩ : T)) (by
    intro a b hab
    change f a.val*(f b.val)⁻¹ ∈ Q
    have hh := hPQ (a.val*b.val⁻¹) hab
    simpa only [map_mul,map_inv] using hh)

/-- Descent preserves the actual local multiplication domain wherever the
source product is defined. -/
def quotientMapHom : LocalGroupHom (hP.quotientAlgebra hW1 hWi hW6)
    (hQ.quotientAlgebra hT1 hTi hT6) where
  toFun := hP.quotientMap hW1 hWi hW6 hQ hT1 hTi hT6 f hPQ hWT
  map_one := by
    change hQ.windowMk hT1 hTi hT6 ⟨f 1,_⟩ = hQ.windowMk hT1 hTi hT6 ⟨1,hT1⟩
    congr 1
    exact Subtype.ext (map_one f)
  map_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      change hQ.windowMk hT1 hTi hT6 ⟨f a.val⁻¹,_⟩ = hQ.windowMk hT1 hTi hT6 ⟨(f a.val)⁻¹,_⟩
      congr 1
      exact Subtype.ext (map_inv f a.val)
  map_mul := by
    rintro x y z ⟨a,b,c,ha,hb,hc,hab⟩
    refine ⟨⟨f a.val,hWT a.val a.property⟩,⟨f b.val,hWT b.val b.property⟩,
      ⟨f c.val,hWT c.val c.property⟩,?_,?_,?_,?_⟩
    · exact congrArg (hP.quotientMap hW1 hWi hW6 hQ hT1 hTi hT6 f hPQ hWT) ha
    · exact congrArg (hP.quotientMap hW1 hWi hW6 hQ hT1 hTi hT6 f hPQ hWT) hb
    · exact congrArg (hP.quotientMap hW1 hWi hW6 hQ hT1 hTi hT6 f hPQ hWT) hc
    · rw [← map_mul,hab]

theorem quotientMap_kernel (a : W) :
    hP.quotientMap hW1 hWi hW6 hQ hT1 hTi hT6 f hPQ hWT (hP.windowMk hW1 hWi hW6 a) =
      (hQ.quotientAlgebra hT1 hTi hT6).one ↔ f a.val ∈ Q := by
  change hQ.windowMk hT1 hTi hT6 ⟨f a.val,_⟩ = hQ.windowMk hT1 hTi hT6 ⟨1,hT1⟩ ↔ _
  rw [window_quotient_eq_iff]
  simp

theorem quotientMap_surjective
    (hsurj : ∀ y ∈ T, ∃ x ∈ W, f x = y) :
    Function.Surjective (hP.quotientMap hW1 hWi hW6 hQ hT1 hTi hT6 f hPQ hWT) := by
  intro y
  induction y using Quotient.inductionOn with
  | h b =>
    obtain ⟨a,ha,hab⟩ := hsurj b.val b.property
    refine ⟨hP.windowMk hW1 hWi hW6 ⟨a,ha⟩,?_⟩
    change hQ.windowMk hT1 hTi hT6 ⟨f a,_⟩ = hQ.windowMk hT1 hTi hT6 b
    congr 1
    exact Subtype.ext hab

/-- The induced quotient map is continuous when the ambient map is continuous. -/
theorem continuous_quotientMap [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (hWo : IsOpen W) (hf : Continuous f) :
    Continuous (hP.quotientMap hW1 hWi hW6 hQ hT1 hTi hT6 f hPQ hWT) := by
  apply (hP.isOpenQuotientMap_windowMk hW1 hWi hW6 hWo).isQuotientMap.continuous_iff.2
  exact (hQ.continuous_windowMk hT1 hTi hT6).comp
    ((hf.comp continuous_subtype_val).subtype_mk _)
end LocalNormalSet
end DirectedCycles
