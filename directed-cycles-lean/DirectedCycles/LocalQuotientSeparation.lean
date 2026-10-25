module

public import DirectedCycles.LocalQuotientContinuity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Compactness.LocallyCompact

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

theorem isOpenQuotientMap_windowMk (hWo : IsOpen W) :
    IsOpenQuotientMap (hP.windowMk hW1 hWi hW6) :=
  ⟨Quotient.mk_surjective,hP.continuous_windowMk hW1 hWi hW6,
    hP.isOpenMap_windowMk hW1 hWi hW6 hWo⟩

/-- Relative closedness in the normalizing region is enough: every difference
of window representatives lies in that region. -/
theorem quotient_relation_closed (hPc : IsClosed (Subtype.val ⁻¹' P : Set V)) :
    IsClosed {p : W × W | hP.windowMk hW1 hWi hW6 p.1 = hP.windowMk hW1 hWi hW6 p.2} := by
  let f : W × W → V := fun p =>
    ⟨p.1.val*p.2.val⁻¹,window_mul_mem hW1 hW6 p.1.property (window_inv_mem hWi p.2.property)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd).inv
  have he : {p : W × W | hP.windowMk hW1 hWi hW6 p.1 = hP.windowMk hW1 hWi hW6 p.2} =
      f ⁻¹' (Subtype.val ⁻¹' P) := by
    ext p
    exact hP.window_quotient_eq_iff hW1 hWi hW6 p.1 p.2
  rw [he]
  exact hPc.preimage hf

/-- The quotient is Hausdorff under the actual relative closedness condition. -/
theorem quotient_t2Space (hWo : IsOpen W) (hPc : IsClosed (Subtype.val ⁻¹' P : Set V)) :
    T2Space (hP.WindowQuotient hW1 hWi hW6) :=
  (t2Space_iff_of_isOpenQuotientMap (hP.isOpenQuotientMap_windowMk hW1 hWi hW6 hWo)).2
    (hP.quotient_relation_closed hW1 hWi hW6 hPc)

theorem quotient_locallyCompactSpace [LocallyCompactSpace G] (hWo : IsOpen W) :
    LocallyCompactSpace (hP.WindowQuotient hW1 hWi hW6) := by
  let : LocallyCompactSpace W := hWo.locallyCompactSpace
  exact (hP.isOpenQuotientMap_windowMk hW1 hWi hW6 hWo).locallyCompactSpace
end LocalNormalSet
end DirectedCycles
