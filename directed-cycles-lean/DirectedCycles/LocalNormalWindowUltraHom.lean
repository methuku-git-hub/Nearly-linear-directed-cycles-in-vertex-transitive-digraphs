module

public import DirectedCycles.LocalNormalWindowQuotientUltra
public import DirectedCycles.LocalCongruenceDivision
public import DirectedCycles.LocalGroupMulEquiv
public import DirectedCycles.LocalApproximateSetImages

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace NormalSubgroupWindow
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (H S : ∀ i, Set (G i)) (W : ∀ i, (L i).NormalSubgroupWindow (H i) (S i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)

noncomputable def quotientUltraHom : LocalGroupHom
    (localUltraAlgebra (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)
      (fun i => (componentCongruence G L H S W hd hr i).algebra))
    (limitCongruence U G L H S W hd hr).algebra := by
  let M := localUltraAlgebra (U : Filter ι) G L
  have hD : M.DivisionClosed := localUltraAlgebra_divisionClosed (U : Filter ι) G L hd
  have hR : M.Reversible := localUltraAlgebra_reversible (U : Filter ι) G L hr
  let V := ultraproduct U G L H S W
  exact LocalGroupHom.ofMulEquiv ((V.congruence hD hR).algebra_cancellative
    (hD.restrict M _ V.one_mem V.inv_mem) (hR.restrict M _ V.one_mem V.inv_mem))
    (quotientUltraEquiv U G L H S W hd hr) (quotientUltraEquiv_mul_iff U G L H S W hd hr)

noncomputable def quotientUltraInvHom : LocalGroupHom
    (limitCongruence U G L H S W hd hr).algebra
    (localUltraAlgebra (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)
      (fun i => (componentCongruence G L H S W hd hr i).algebra)) :=
  LocalGroupHom.inverseOfMulEquiv (localUltraAlgebra_cancellative (U : Filter ι) _ _ (fun i => by
    have hRi : (L i).Reversible := hr i
    exact ((W i).congruence (hd i) (hr i)).algebra_cancellative
      ((hd i).restrict (L i) _ (W i).one_mem (W i).inv_mem)
      (hRi.restrict (L i) _ (W i).one_mem (W i).inv_mem)))
    (quotientUltraEquiv U G L H S W hd hr) (quotientUltraEquiv_mul_iff U G L H S W hd hr)

theorem quotientUltraEquiv_projection (a : LocalUltraproduct (U : Filter ι) (fun i => S i)) :
    quotientUltraEquiv U G L H S W hd hr
      (LocalGroupCongruence.ultraProjection (U : Filter ι) (fun i => S i)
        (fun i => (W i).restricted) (componentCongruence G L H S W hd hr) a) =
      (limitCongruence U G L H S W hd hr).project (windowEquiv U G L H S W a) := by
  dsimp only [quotientUltraEquiv,Equiv.trans_apply]
  rw [← LocalGroupCongruence.quotientUltraEquiv_project,Equiv.symm_apply_apply,
    LocalGroupCongruence.transportEquiv_project]

/-- The actual projected internal set is the image, under the canonical
quotient equivalence, of the internal family of component projected sets. -/
theorem quotientUltraEquiv_internal_image (B : ∀ i, Set (S i)) :
    quotientUltraEquiv U G L H S W hd hr ''
      localUltraSet (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)
        (fun i => (componentCongruence G L H S W hd hr i).project '' B i) =
      (limitCongruence U G L H S W hd hr).project ''
        (windowEquiv U G L H S W '' localUltraSet (U : Filter ι) (fun i => S i) B) := by
  rw [← localUltraMap_image (U : Filter ι) (fun i => S i)
    (fun i => (componentCongruence G L H S W hd hr i).Carrier)
    (fun i => ⟨(L i).one,(W i).one_mem⟩) (fun i => (componentCongruence G L H S W hd hr i).project) B,
    Set.image_image,Set.image_image]
  apply Set.image_congr
  intro a _
  exact quotientUltraEquiv_projection U G L H S W hd hr a
end NormalSubgroupWindow
end LocalGroupAlgebra
end DirectedCycles
