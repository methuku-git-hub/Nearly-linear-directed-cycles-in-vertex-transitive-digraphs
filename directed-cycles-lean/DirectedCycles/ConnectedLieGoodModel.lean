import DirectedCycles.OpenSubgroupGoodModel
import DirectedCycles.OpenSubgroupLieGroup
import DirectedCycles.ConnectedModelRestriction
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
open scoped Manifold ContDiff
namespace DirectedCycles
universe u
variable {G : Type u} [Group G] {T : Set G} {Internal : Set G → Prop}
    (M : InternalLocallyCompactGroupModel G T Internal)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M.carrier]

include E

/-- The identity component of the chosen Lie target is open. The component
is chosen after the model and its compact kernel, not uniformly before them. -/
theorem lie_model_component_open :
    IsOpen (Subgroup.connectedComponentOfOne M.carrier : Set M.carrier) := by
  let : LocallyConnectedSpace M.carrier := ChartedSpace.locallyConnectedSpace E M.carrier
  exact isOpen_connectedComponent

/-- Actual connected restriction of the supplied Lie good model. -/
noncomputable def connectedLieGoodModel :
    InternalLocallyCompactGroupModel ((Subgroup.connectedComponentOfOne M.carrier).comap M.map)
      (((Subgroup.connectedComponentOfOne M.carrier).comap M.map).subtype ⁻¹' T)
      (RestrictedInternal ((Subgroup.connectedComponentOfOne M.carrier).comap M.map) Internal) :=
  openSubgroupGoodModel M (Subgroup.connectedComponentOfOne M.carrier)
    (lie_model_component_open (E := E) M)

theorem connectedLieGoodModel_connected :
    ConnectedSpace (connectedLieGoodModel (E := E) M).carrier :=
  connectedModelRestriction_target_connected

theorem connectedLieGoodModel_lie [LieGroup 𝓘(ℝ,E) ∞ M.carrier] :
    let : ChartedSpace E (connectedLieGoodModel (E := E) M).carrier :=
      openSubgroupChartedSpace (E := E) (Subgroup.connectedComponentOfOne M.carrier)
      (lie_model_component_open (E := E) M)
    LieGroup 𝓘(ℝ,E) ∞ (connectedLieGoodModel (E := E) M).carrier :=
  open_subgroup_lie_group (Subgroup.connectedComponentOfOne M.carrier)
    (lie_model_component_open (E := E) M)

/-- The connected restriction has exactly the original kernel, embedded
back in the original source. -/
theorem connectedLieGoodModel_kernel :
    ((Subgroup.connectedComponentOfOne M.carrier).comap M.map).subtype ''
      ((connectedLieGoodModel (E := E) M).map.ker : Set _) = (M.map.ker : Set G) :=
  connectedModelRestriction_kernel M.map
end DirectedCycles
