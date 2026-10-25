module

public import DirectedCycles.LocalCentralQuotientUltraData
public import DirectedCycles.LocalUltraproductMaps
public import DirectedCycles.SurjectiveKernelEquiv

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))

abbrev componentProjection : LocalUltraproduct (U : Filter ι) (fun i => (D i).small) →
    LocalUltraproduct (U : Filter ι) (fun i => (D i).Carrier) :=
  localUltraMap (U : Filter ι) _ _ (fun i => (D i).project)

abbrev limitProjection : LocalUltraproduct (U : Filter ι) (fun i => (D i).small) →
    (ultraproduct U G L P D).Carrier :=
  (ultraproduct U G L P D).project ∘ localUltraWindowMap (U : Filter ι) G (fun i => (D i).small)

theorem componentProjection_surjective : Function.Surjective (componentProjection U G L P D) :=
  localUltraMap_surjective _ _ _ _ (fun _ => Quotient.mk_surjective)

theorem limitProjection_surjective : Function.Surjective (limitProjection U G L P D) :=
  Quotient.mk_surjective.comp (localUltraWindowMap_surjective (U : Filter ι) G L _ (fun i => (D i).one_mem))

/-- The component quotient and the quotient of the internal progression
have exactly the same kernel on actual small-window representatives. -/
theorem quotient_projections_same_kernel (x y : LocalUltraproduct (U : Filter ι) (fun i => (D i).small)) :
    componentProjection U G L P D x = componentProjection U G L P D y ↔
      limitProjection U G L P D x = limitProjection U G L P D y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  change localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i)) =
    localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (b i)) ↔ _
  rw [localUltraMk_eq_iff]
  have hlim := (ultraproduct U G L P D).project_eq_iff
    (localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) (localUltraMk _ _ a))
    (localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) (localUltraMk _ _ b))
  have hrel := localUltraBinaryRelation_mk_iff (U : Filter ι) G (fun i => (D i).equivalence.Rel)
    (fun i => (a i).val) (fun i => (b i).val)
  exact (Filter.eventually_congr (Filter.Eventually.of_forall fun i =>
    (D i).project_eq_iff (a i) (b i))).trans (hrel.symm.trans hlim.symm)

noncomputable def quotientUltraEquiv : LocalUltraproduct (U : Filter ι) (fun i => (D i).Carrier) ≃
    (ultraproduct U G L P D).Carrier :=
  surjectiveKernelEquiv (componentProjection U G L P D) (limitProjection U G L P D)
    (componentProjection_surjective U G L P D) (limitProjection_surjective U G L P D)
    (quotient_projections_same_kernel U G L P D)

theorem quotientUltraEquiv_projection (a : LocalUltraproduct (U : Filter ι) (fun i => (D i).small)) :
    quotientUltraEquiv U G L P D (componentProjection U G L P D a) = limitProjection U G L P D a :=
  surjectiveKernelEquiv_apply _ _ _ _ _ a
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
