module

public import DirectedCycles.LocalQuotientAssociativity
public import DirectedCycles.LocalGroupTopology
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Saturating a set in the window means multiplying by P itself. -/
theorem window_saturation (S : Set W) :
    (hP.windowMk hW1 hWi hW6) ⁻¹' ((hP.windowMk hW1 hWi hW6) '' S) =
      Subtype.val ⁻¹' (P * (Subtype.val '' S)) := by
  ext x
  constructor
  · rintro ⟨y,hy,he⟩
    have hp : x.val*y.val⁻¹ ∈ P := Quotient.exact he.symm
    exact ⟨x.val*y.val⁻¹,hp,y.val,⟨y,hy,rfl⟩,by simp [mul_assoc]⟩
  · rintro ⟨p,hp,y,⟨y',hy,rfl⟩,he⟩
    refine ⟨y',hy,?_⟩
    apply Eq.symm
    apply Quotient.sound
    change x.val*y'.val⁻¹ ∈ P
    rw [← he]
    simpa [mul_assoc] using hp

omit [IsTopologicalGroup G] in
theorem continuous_windowMk : Continuous (hP.windowMk hW1 hWi hW6) :=
  continuous_quot_mk

/-- On an open window the actual local quotient map is open. -/
theorem isOpenMap_windowMk (hWo : IsOpen W) : IsOpenMap (hP.windowMk hW1 hWi hW6) := by
  intro S hS
  rw [isOpen_coinduced]
  change IsOpen ((hP.windowMk hW1 hWi hW6) ⁻¹' ((hP.windowMk hW1 hWi hW6) '' S))
  rw [window_saturation]
  exact (hWo.isOpenMap_subtype_val S hS).mul_left.preimage continuous_subtype_val

theorem continuous_quotientInv : Continuous (hP.quotientInv hW1 hWi hW6) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.2
  exact (hP.continuous_windowMk hW1 hWi hW6).comp
    ((ContinuousInv.continuous_inv.comp continuous_subtype_val).subtype_mk fun x => window_inv_mem hWi x.property)

/-- The pairs whose product already lies in the window before taking cosets. -/
def windowProductDomain : Set (W × W) := {p | p.1.val*p.2.val ∈ W}

theorem isOpen_windowProductDomain (hWo : IsOpen W) : IsOpen (windowProductDomain (W := W)) :=
  hWo.preimage ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The quotient multiplication domain is the open image of the actual
representative multiplication domain. -/
theorem quotient_domain_eq_image :
    {p | (hP.quotientAlgebra hW1 hWi hW6).Defined p.1 p.2} =
      (Prod.map (hP.windowMk hW1 hWi hW6) (hP.windowMk hW1 hWi hW6)) ''
        windowProductDomain (W := W) := by
  ext p
  constructor
  · rintro ⟨z,a,b,c,ha,hb,_,hab⟩
    refine ⟨(a,b),?_,?_⟩
    · change a.val*b.val ∈ W
      rw [hab]; exact c.property
    · exact Prod.ext ha hb
  · rintro ⟨⟨a,b⟩,hab,rfl⟩
    exact ⟨hP.windowMk hW1 hWi hW6 ⟨a.val*b.val,hab⟩,
      a,b,⟨a.val*b.val,hab⟩,rfl,rfl,rfl,rfl⟩

theorem isOpen_quotientDomain (hWo : IsOpen W) :
    IsOpen {p : hP.WindowQuotient hW1 hWi hW6 × hP.WindowQuotient hW1 hWi hW6 | (hP.quotientAlgebra hW1 hWi hW6).Defined p.1 p.2} := by
  rw [hP.quotient_domain_eq_image]
  exact ((hP.isOpenMap_windowMk hW1 hWi hW6 hWo).prodMap
    (hP.isOpenMap_windowMk hW1 hWi hW6 hWo)) _ (isOpen_windowProductDomain hWo)
end LocalNormalSet
end DirectedCycles
