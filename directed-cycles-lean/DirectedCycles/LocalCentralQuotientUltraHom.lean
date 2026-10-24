import DirectedCycles.LocalCentralQuotientUltraProducts
import DirectedCycles.LocalGroupMulEquiv
import DirectedCycles.LocalEscapeMaps
import DirectedCycles.LocalInternalImages

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)

noncomputable def quotientUltraHom : LocalGroupHom
    (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra))
    (ultraproduct U G L P D).algebra :=
  LocalGroupHom.ofMulEquiv ((ultraproduct U G L P D).algebra_cancellative
    (localUltraAlgebra_divisionClosed (U : Filter ι) G L hd)
    (localUltraAlgebra_reversible (U : Filter ι) G L hr))
    (quotientUltraEquiv U G L P D) (quotientUltraEquiv_mul_iff U G L P D)

noncomputable def quotientUltraInvHom : LocalGroupHom (ultraproduct U G L P D).algebra
    (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra)) :=
  LocalGroupHom.inverseOfMulEquiv
    (localUltraAlgebra_cancellative (U : Filter ι) _ _ (fun i => (D i).algebra_cancellative (hd i) (hr i)))
    (quotientUltraEquiv U G L P D) (quotientUltraEquiv_mul_iff U G L P D)

/-- The quotient of the internal progression carries exactly the projected
internal family of component sets. -/
theorem quotientUltraEquiv_internal_image (B : ∀ i, Set (D i).small) :
    quotientUltraEquiv U G L P D '' localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
      (fun i => (D i).project '' B i) =
      (ultraproduct U G L P D).project ''
        (localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) ''
          localUltraSet (U : Filter ι) (fun i => (D i).small) B) := by
  rw [← localUltraMap_image (U : Filter ι) (fun i => (D i).small) (fun i => (D i).Carrier)
    (fun i => ⟨(L i).one,(D i).one_mem⟩) (fun i => (D i).project) B,
    Set.image_image,Set.image_image]
  apply Set.image_congr
  intro a _
  exact quotientUltraEquiv_projection U G L P D a

include hd hr in
/-- Escape norms agree exactly under the actual local quotient equivalence. -/
theorem quotientUltraEquiv_escapeNorm
    (A : Set (LocalUltraproduct (U : Filter ι) (fun i => (D i).Carrier)))
    (hA : (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra)).one ∈ A)
    (x : LocalUltraproduct (U : Filter ι) (fun i => (D i).Carrier)) :
    (ultraproduct U G L P D).algebra.escapeNorm ((quotientUltraEquiv U G L P D) '' A) (quotientUltraEquiv U G L P D x) =
      (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra)).escapeNorm A x := by
  let E := quotientUltraEquiv U G L P D
  have hf := escapeNorm_image_le _ (quotientUltraHom U G L P D hd hr) hA x
  apply le_antisymm hf
  change (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier)
    (fun i => (D i).algebra)).escapeNorm A x ≤
    (ultraproduct U G L P D).algebra.escapeNorm (E '' A) (E x)
  have hAi : (ultraproduct U G L P D).algebra.one ∈ E '' A :=
    ⟨_,hA,(quotientUltraHom U G L P D hd hr).map_one⟩
  have hb := escapeNorm_image_le _ (quotientUltraInvHom U G L P D hd hr) hAi (E x)
  have he : E.symm '' (E '' A) = A := by
    ext y
    constructor
    · rintro ⟨z,⟨w,hw,rfl⟩,rfl⟩
      simpa only [E.symm_apply_apply] using hw
    · exact fun hy => ⟨E y,⟨y,hy,rfl⟩,E.symm_apply_apply y⟩
  change _ ≤ _ at hb
  simpa only [show (quotientUltraInvHom U G L P D hd hr).toFun = E.symm from rfl,he,E.symm_apply_apply] using hb
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
