module

public import DirectedCycles.LocalQuotientData
public import DirectedCycles.WindowUltraproductEquiv
public import DirectedCycles.LocalUltraproductMaps
public import DirectedCycles.SurjectiveKernelEquiv

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalQuotientData
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (D : ∀ i, LocalQuotientData (G i))

abbrev componentProjection : LocalUltraproduct F (fun i => (D i).W) →
    LocalUltraproduct F (fun i => (D i).Carrier) :=
  localUltraMap F (fun i => (D i).W) (fun i => (D i).Carrier) (fun i => (D i).project)

abbrev limitProjection : LocalUltraproduct F (fun i => (D i).W) →
    (ultraproduct F G D).Carrier :=
  (ultraproduct F G D).project ∘ ultraWindowMap F G (fun i => (D i).W)

theorem componentProjection_surjective : Function.Surjective (componentProjection F G D) :=
  localUltraMap_surjective F _ _ _ (fun _ => Quotient.mk_surjective)

theorem limitProjection_surjective : Function.Surjective (limitProjection F G D) :=
  Quotient.mk_surjective.comp (ultraWindowMap_surjective F G (fun i => (D i).W) (fun i => (D i).one_mem))

/-- The two quotient constructions have exactly the same equivalence
relation on actual window representatives. -/
theorem quotient_projections_same_kernel (x y : LocalUltraproduct F (fun i => (D i).W)) :
    componentProjection F G D x = componentProjection F G D y ↔
      limitProjection F G D x = limitProjection F G D y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  change localUltraMk F (fun i => (D i).Carrier) (fun i => (D i).project (a i)) =
      localUltraMk F (fun i => (D i).Carrier) (fun i => (D i).project (b i)) ↔ _
  rw [localUltraMk_eq_iff]
  change _ ↔ (ultraproduct F G D).project (ultraWindowMap F G (fun i => (D i).W) (localUltraMk F _ a)) =
    (ultraproduct F G D).project (ultraWindowMap F G (fun i => (D i).W) (localUltraMk F _ b))
  rw [project_eq_iff]
  change _ ↔ ultraMk F G (fun i => (a i).val)*(ultraMk F G (fun i => (b i).val))⁻¹ ∈
    ultraSet F G (fun i => (D i).P)
  rw [← map_inv,← map_mul,ultraMk_mem_ultraSet_iff]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun i => (D i).project_eq_iff (a i) (b i))

/-- The ultraproduct of the actual local coset spaces is equivalent to the
actual local coset space of the internal sets. -/
noncomputable def quotientUltraEquiv : LocalUltraproduct F (fun i => (D i).Carrier) ≃
    (ultraproduct F G D).Carrier :=
  surjectiveKernelEquiv (componentProjection F G D) (limitProjection F G D)
    (componentProjection_surjective F G D) (limitProjection_surjective F G D)
    (quotient_projections_same_kernel F G D)

theorem quotientUltraEquiv_projection (a : LocalUltraproduct F (fun i => (D i).W)) :
    quotientUltraEquiv F G D (componentProjection F G D a) = limitProjection F G D a :=
  surjectiveKernelEquiv_apply _ _ _ _ _ a
end LocalQuotientData
end DirectedCycles
