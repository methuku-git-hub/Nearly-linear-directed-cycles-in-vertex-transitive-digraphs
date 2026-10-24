import DirectedCycles.LocalCongruenceUltraproduct
import DirectedCycles.LocalInternalImages
import DirectedCycles.LocalEscapeMaps

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupCongruence
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (C : ∀ i, LocalGroupCongruence (L i))

noncomputable def quotientUltraHom : LocalGroupHom (ultraproduct F G L C).algebra
    (localUltraAlgebra F (fun i => (C i).Carrier) (fun i => (C i).algebra)) where
  toFun := quotientUltraEquiv F G L C
  map_one := (ultraProjectionHom F G L C).map_one
  map_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact (ultraProjectionHom F G L C).map_inv x
  map_mul := fun {x y z} hm => (quotientUltraEquiv_mul_iff F G L C x y z).1 hm

noncomputable def quotientUltraInvHom : LocalGroupHom
    (localUltraAlgebra F (fun i => (C i).Carrier) (fun i => (C i).algebra))
    (ultraproduct F G L C).algebra where
  toFun := (quotientUltraEquiv F G L C).symm
  map_one := by
    apply (quotientUltraEquiv F G L C).injective
    rw [(quotientUltraEquiv F G L C).apply_symm_apply]
    exact (quotientUltraHom F G L C).map_one.symm
  map_inv := by
    intro x
    apply (quotientUltraEquiv F G L C).injective
    rw [(quotientUltraEquiv F G L C).apply_symm_apply]
    simpa only [show (quotientUltraHom F G L C).toFun = quotientUltraEquiv F G L C from rfl,
      (quotientUltraEquiv F G L C).apply_symm_apply] using
      ((quotientUltraHom F G L C).map_inv ((quotientUltraEquiv F G L C).symm x)).symm
  map_mul := by
    intro x y z hm
    apply (quotientUltraEquiv_mul_iff F G L C _ _ _).2
    simpa only [(quotientUltraEquiv F G L C).apply_symm_apply] using hm

/-- An actual internal image in the quotient of the ultraproduct corresponds
exactly to the internal family of component quotient images. -/
theorem quotientUltraEquiv_internal_image (A : ∀ i, Set (G i)) :
    quotientUltraEquiv F G L C '' ((ultraproduct F G L C).project '' localUltraSet F G A) =
      localUltraSet F (fun i => (C i).Carrier) (fun i => (C i).project '' A i) := by
  rw [Set.image_image]
  exact localUltraMap_image F G _ (fun i => (L i).one) (fun i => (C i).project) A

/-- Escape is preserved by the actual quotient-ultraproduct equivalence. -/
theorem quotientUltraEquiv_escapeNorm (A : Set (ultraproduct F G L C).Carrier)
    (hA : (ultraproduct F G L C).algebra.one ∈ A) (x : (ultraproduct F G L C).Carrier) :
    (localUltraAlgebra F (fun i => (C i).Carrier) (fun i => (C i).algebra)).escapeNorm
      (quotientUltraEquiv F G L C '' A) (quotientUltraEquiv F G L C x) =
      (ultraproduct F G L C).algebra.escapeNorm A x := by
  let E := quotientUltraEquiv F G L C
  have hf := LocalGroupAlgebra.escapeNorm_image_le _ (quotientUltraHom F G L C) hA x
  apply le_antisymm hf
  have hA' : (localUltraAlgebra F (fun i => (C i).Carrier) (fun i => (C i).algebra)).one ∈ E '' A :=
    ⟨_,hA,(quotientUltraHom F G L C).map_one⟩
  have hb := LocalGroupAlgebra.escapeNorm_image_le _ (quotientUltraInvHom F G L C) hA' (E x)
  have he : E.symm '' (E '' A) = A := by
    ext y
    constructor
    · rintro ⟨z,⟨w,hw,rfl⟩,rfl⟩
      simpa only [E.symm_apply_apply] using hw
    · exact fun hy => ⟨E y,⟨y,hy,rfl⟩,E.symm_apply_apply y⟩
  change (ultraproduct F G L C).algebra.escapeNorm A x ≤
    (localUltraAlgebra F (fun i => (C i).Carrier) (fun i => (C i).algebra)).escapeNorm (E '' A) (E x)
  simpa only [show (quotientUltraInvHom F G L C).toFun = E.symm from rfl,he,E.symm_apply_apply] using hb
end LocalGroupCongruence
end DirectedCycles
