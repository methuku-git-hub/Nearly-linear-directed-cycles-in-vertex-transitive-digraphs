import DirectedCycles.LocalQuotientUltraproductProducts
import DirectedCycles.LocalGroupMulEquiv
import DirectedCycles.LocalEscapeMaps

set_option autoImplicit false
namespace DirectedCycles
namespace LocalQuotientData
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (D : ∀ i, LocalQuotientData (G i))

noncomputable def quotientUltraHom : LocalGroupHom
    (localUltraAlgebra F (fun i => (D i).Carrier) (fun i => (D i).algebra))
    (ultraproduct F G D).algebra :=
  LocalGroupHom.ofMulEquiv
    ((ultraproduct F G D).localNormal.quotientAlgebra_cancellative
      (ultraproduct F G D).one_mem (ultraproduct F G D).inv_eq (ultraproduct F G D).sixth_subset)
    (quotientUltraEquiv F G D) (quotientUltraEquiv_mul_iff F G D)

noncomputable def quotientUltraInvHom : LocalGroupHom (ultraproduct F G D).algebra
    (localUltraAlgebra F (fun i => (D i).Carrier) (fun i => (D i).algebra)) :=
  LocalGroupHom.inverseOfMulEquiv
    (localUltraAlgebra_cancellative F _ _ (fun i => (D i).localNormal.quotientAlgebra_cancellative
      (D i).one_mem (D i).inv_eq (D i).sixth_subset))
    (quotientUltraEquiv F G D) (quotientUltraEquiv_mul_iff F G D)

/-- Escape norms agree under the actual quotient-ultraproduct equivalence. -/
theorem quotientUltraEquiv_escapeNorm (A : Set (LocalUltraproduct F (fun i => (D i).Carrier)))
    (hA : (localUltraAlgebra F (fun i => (D i).Carrier) (fun i => (D i).algebra)).one ∈ A)
    (x : LocalUltraproduct F (fun i => (D i).Carrier)) :
    (ultraproduct F G D).algebra.escapeNorm ((quotientUltraEquiv F G D) '' A) (quotientUltraEquiv F G D x) =
      (localUltraAlgebra F (fun i => (D i).Carrier) (fun i => (D i).algebra)).escapeNorm A x := by
  let E := quotientUltraEquiv F G D
  have hforward := LocalGroupAlgebra.escapeNorm_image_le _ (quotientUltraHom F G D) hA x
  apply le_antisymm hforward
  change (localUltraAlgebra F (fun i => (D i).Carrier) (fun i => (D i).algebra)).escapeNorm A x ≤
    (ultraproduct F G D).algebra.escapeNorm (E '' A) (E x)
  have hAi : (ultraproduct F G D).algebra.one ∈ E '' A := by
    refine ⟨_,hA,?_⟩
    exact (quotientUltraHom F G D).map_one
  have hback := LocalGroupAlgebra.escapeNorm_image_le _ (quotientUltraInvHom F G D) hAi (E x)
  have he : E.symm '' (E '' A) = A := by
    ext y
    constructor
    · rintro ⟨z,⟨w,hw,rfl⟩,rfl⟩
      simpa only [E.symm_apply_apply] using hw
    · intro hy
      exact ⟨E y,⟨y,hy,rfl⟩,E.symm_apply_apply y⟩
  change _ ≤ _ at hback
  simpa only [show (quotientUltraInvHom F G D).toFun = E.symm from rfl,he,E.symm_apply_apply] using hback
end LocalQuotientData
end DirectedCycles
