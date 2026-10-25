module

public import DirectedCycles.LocalNormalWindowUltraRelation
public import DirectedCycles.LocalCongruenceUltraHom
public import DirectedCycles.LocalCongruenceTransport

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace NormalSubgroupWindow
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (H S : ∀ i, Set (G i)) (W : ∀ i, (L i).NormalSubgroupWindow (H i) (S i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)

/-- Quotients by actual internal normal subgroups commute with local
ultraproducts. The target is the actual normal-subgroup quotient of the
internal window, not a newly postulated local-group structure. -/
noncomputable def quotientUltraEquiv :
    LocalUltraproduct (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier) ≃
      (limitCongruence U G L H S W hd hr).Carrier :=
  (LocalGroupCongruence.quotientUltraEquiv (U : Filter ι) (fun i => S i)
    (fun i => (W i).restricted) (componentCongruence G L H S W hd hr)).symm.trans
      (LocalGroupCongruence.transportEquiv (componentUltraCongruence U G L H S W hd hr)
        (limitCongruence U G L H S W hd hr) (windowEquiv U G L H S W)
        (ultra_relation_iff U G L H S W hd hr))

/-- The quotient equivalence reflects multiplication domains in both
directions, so it cannot silently complete an undefined product. -/
theorem quotientUltraEquiv_mul_iff (x y z :
    LocalUltraproduct (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)) :
    (localUltraAlgebra (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)
      (fun i => (componentCongruence G L H S W hd hr i).algebra)).mulRel x y z ↔
    (limitCongruence U G L H S W hd hr).algebra.mulRel
      (quotientUltraEquiv U G L H S W hd hr x) (quotientUltraEquiv U G L H S W hd hr y)
      (quotientUltraEquiv U G L H S W hd hr z) := by
  let E := LocalGroupCongruence.quotientUltraEquiv (U : Filter ι) (fun i => S i)
    (fun i => (W i).restricted) (componentCongruence G L H S W hd hr)
  have hE := LocalGroupCongruence.quotientUltraEquiv_mul_iff (U : Filter ι) (fun i => S i)
    (fun i => (W i).restricted) (componentCongruence G L H S W hd hr) (E.symm x) (E.symm y) (E.symm z)
  change (componentUltraCongruence U G L H S W hd hr).algebra.mulRel (E.symm x) (E.symm y) (E.symm z) ↔
    (localUltraAlgebra (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)
      (fun i => (componentCongruence G L H S W hd hr i).algebra)).mulRel (E (E.symm x)) (E (E.symm y)) (E (E.symm z)) at hE
  have hE' : (localUltraAlgebra (U : Filter ι) (fun i => (componentCongruence G L H S W hd hr i).Carrier)
      (fun i => (componentCongruence G L H S W hd hr i).algebra)).mulRel x y z ↔
      (componentUltraCongruence U G L H S W hd hr).algebra.mulRel (E.symm x) (E.symm y) (E.symm z) := by
    simpa only [E.apply_symm_apply] using hE.symm
  exact hE'.trans (LocalGroupCongruence.transportEquiv_mul_iff
    (componentUltraCongruence U G L H S W hd hr) (limitCongruence U G L H S W hd hr)
    (windowEquiv U G L H S W) (ultra_relation_iff U G L H S W hd hr)
    (localUltraWindowEquiv_mul_iff (U : Filter ι) G L S (fun i => (W i).one_mem) (fun i => (W i).inv_mem)) _ _ _)
end NormalSubgroupWindow
end LocalGroupAlgebra
end DirectedCycles
