import DirectedCycles.LocalQuotientTopology

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The map from actual representative pairs to the local quotient domain. -/
def quotientDomainMap (p : windowProductDomain (W := W)) :
    {p : hP.WindowQuotient hW1 hWi hW6 × hP.WindowQuotient hW1 hWi hW6 | (hP.quotientAlgebra hW1 hWi hW6).Defined p.1 p.2} :=
  ⟨(hP.windowMk hW1 hWi hW6 p.val.1,hP.windowMk hW1 hWi hW6 p.val.2),
    ⟨hP.windowMk hW1 hWi hW6 ⟨p.val.1.val*p.val.2.val,p.property⟩,
      p.val.1,p.val.2,⟨p.val.1.val*p.val.2.val,p.property⟩,rfl,rfl,rfl,rfl⟩⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientDomainMap_surjective : Function.Surjective (hP.quotientDomainMap hW1 hWi hW6) := by
  rintro ⟨p,z,a,b,c,ha,hb,_,hab⟩
  have hp : a.val*b.val ∈ W := by rw [hab]; exact c.property
  refine ⟨⟨(a,b),hp⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext ha hb

omit [IsTopologicalGroup G] in
theorem continuous_quotientDomainMap : Continuous (hP.quotientDomainMap hW1 hWi hW6) := by
  apply Continuous.subtype_mk
  exact ((hP.continuous_windowMk hW1 hWi hW6).comp continuous_subtype_val.fst).prodMk
    ((hP.continuous_windowMk hW1 hWi hW6).comp continuous_subtype_val.snd)

theorem isOpenMap_quotientDomainMap (hWo : IsOpen W) :
    IsOpenMap (hP.quotientDomainMap hW1 hWi hW6) := by
  have hq := hP.isOpenMap_windowMk hW1 hWi hW6 hWo
  have hd := isOpen_windowProductDomain hWo
  exact ((hq.prodMap hq).comp hd.isOpenMap_subtype_val).subtype_mk _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotient_mul_at_representatives (p : windowProductDomain (W := W)) :
    (hP.quotientAlgebra hW1 hWi hW6).mul
      (hP.quotientDomainMap hW1 hWi hW6 p).val.1
      (hP.quotientDomainMap hW1 hWi hW6 p).val.2
      (hP.quotientDomainMap hW1 hWi hW6 p).property =
        hP.windowMk hW1 hWi hW6 ⟨p.val.1.val*p.val.2.val,p.property⟩ := by
  apply (hP.quotientAlgebra hW1 hWi hW6).unique
    ((hP.quotientAlgebra hW1 hWi hW6).mul_spec _ _ _)
  exact ⟨p.val.1,p.val.2,⟨p.val.1.val*p.val.2.val,p.property⟩,rfl,rfl,rfl,rfl⟩

/-- Multiplication is continuous on its exact partial domain, by the open
surjection from pairs of representatives; no choice of continuous section is
postulated. -/
theorem continuous_quotientMul (hWo : IsOpen W) :
    Continuous (fun p : {p : hP.WindowQuotient hW1 hWi hW6 × hP.WindowQuotient hW1 hWi hW6 | (hP.quotientAlgebra hW1 hWi hW6).Defined p.1 p.2} =>
      (hP.quotientAlgebra hW1 hWi hW6).mul p.val.1 p.val.2 p.property) := by
  have hq := (hP.isOpenMap_quotientDomainMap hW1 hWi hW6 hWo).isQuotientMap
    (hP.continuous_quotientDomainMap hW1 hWi hW6)
    (hP.quotientDomainMap_surjective hW1 hWi hW6)
  apply hq.continuous_iff.2
  have he : (fun p : windowProductDomain (W := W) =>
      (hP.quotientAlgebra hW1 hWi hW6).mul
        (hP.quotientDomainMap hW1 hWi hW6 p).val.1
        (hP.quotientDomainMap hW1 hWi hW6 p).val.2
        (hP.quotientDomainMap hW1 hWi hW6 p).property) =
      (fun p => hP.windowMk hW1 hWi hW6 ⟨p.val.1.val*p.val.2.val,p.property⟩) := by
    funext p
    exact hP.quotient_mul_at_representatives hW1 hWi hW6 p
  change Continuous (fun p : windowProductDomain (W := W) =>
      (hP.quotientAlgebra hW1 hWi hW6).mul
        (hP.quotientDomainMap hW1 hWi hW6 p).val.1
        (hP.quotientDomainMap hW1 hWi hW6 p).val.2
        (hP.quotientDomainMap hW1 hWi hW6 p).property)
  rw [he]
  apply (hP.continuous_windowMk hW1 hWi hW6).comp
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_subtype_val.fst).mul
    (continuous_subtype_val.comp continuous_subtype_val.snd)

/-- The actual window quotient, with its quotient topology, is a topological
local group. Hausdorffness requires a separate closed-relation argument. -/
theorem quotientAlgebra_topology (hWo : IsOpen W) :
    LocalGroupTopology (hP.quotientAlgebra hW1 hWi hW6) where
  continuous_inv := hP.continuous_quotientInv hW1 hWi hW6
  isOpen_domain := hP.isOpen_quotientDomain hW1 hWi hW6 hWo
  continuous_mul := hP.continuous_quotientMul hW1 hWi hW6 hWo
end LocalNormalSet
end DirectedCycles
