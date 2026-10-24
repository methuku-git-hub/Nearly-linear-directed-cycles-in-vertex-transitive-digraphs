import DirectedCycles.LieQuotientData
import DirectedCycles.ConnectedLieGoodModel
import DirectedCycles.GoodModelFiniteCover

set_option autoImplicit false
open scoped Manifold ContDiff
namespace DirectedCycles
universe u
variable {G : Type u} [Group G] {T : Set G} {Internal : Set G → Prop}

/-- The connected Lie model constructed from specified compact quotient
data, retaining the actual source preimages and internal-set predicates. -/
noncomputable def connectedLieQuotientModel
    (M : InternalLocallyCompactGroupModel G T Internal)
    (D : LieQuotientData M.carrier M.neighbourhood) :=
  let Q := lieQuotientGoodModel M D
  let : ChartedSpace (EuclideanSpace ℝ (Fin D.dimension)) Q.carrier := D.charts
  connectedLieGoodModel (E := EuclideanSpace ℝ (Fin D.dimension)) Q

theorem connectedLieQuotientModel_connected
    (M : InternalLocallyCompactGroupModel G T Internal)
    (D : LieQuotientData M.carrier M.neighbourhood) :
    ConnectedSpace (connectedLieQuotientModel M D).carrier := by
  let Q := lieQuotientGoodModel M D
  let : ChartedSpace (EuclideanSpace ℝ (Fin D.dimension)) Q.carrier := D.charts
  exact connectedLieGoodModel_connected (E := EuclideanSpace ℝ (Fin D.dimension)) Q

theorem connectedLieQuotientModel_lie
    (M : InternalLocallyCompactGroupModel G T Internal)
    (D : LieQuotientData M.carrier M.neighbourhood) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin D.dimension)) (connectedLieQuotientModel M D).carrier,
      let := cs
      LieGroup 𝓘(ℝ,EuclideanSpace ℝ (Fin D.dimension)) ∞ (connectedLieQuotientModel M D).carrier := by
  let Q := lieQuotientGoodModel M D
  let E := EuclideanSpace ℝ (Fin D.dimension)
  let : ChartedSpace E Q.carrier := D.charts
  let : LieGroup 𝓘(ℝ,E) ∞ Q.carrier := lieQuotientGoodModel_lie M D
  exact ⟨openSubgroupChartedSpace (E := E) (Subgroup.connectedComponentOfOne Q.carrier)
      (lie_model_component_open (E := E) Q),connectedLieGoodModel_lie Q⟩

/-- The first source restriction and compact quotient lose no hidden
kernel: the kernel is exactly the specified compact-kernel preimage. -/
theorem lieQuotientGoodModel_kernel
    (M : InternalLocallyCompactGroupModel G T Internal)
    (D : LieQuotientData M.carrier M.neighbourhood) :
    (lieQuotientGoodModel M D).map.ker =
      D.kernel.comap (subgroupModelHom M.map D.source) := by
  let : D.kernel.Normal := D.normal
  ext x
  change (QuotientGroup.mk' D.kernel) (subgroupModelHom M.map D.source x) = 1 ↔
    subgroupModelHom M.map D.source x ∈ D.kernel
  exact QuotientGroup.eq_one_iff _

/-- The second, connected restriction preserves precisely that kernel in
the first restricted source. -/
theorem connectedLieQuotientModel_kernel
    (M : InternalLocallyCompactGroupModel G T Internal)
    (D : LieQuotientData M.carrier M.neighbourhood) :
    let Q := lieQuotientGoodModel M D
    ((Subgroup.connectedComponentOfOne Q.carrier).comap Q.map).subtype ''
      ((connectedLieQuotientModel M D).map.ker : Set _) =
      (D.kernel.comap (subgroupModelHom M.map D.source) : Set _) := by
  let Q := lieQuotientGoodModel M D
  let : ChartedSpace (EuclideanSpace ℝ (Fin D.dimension)) Q.carrier := D.charts
  have he := connectedLieGoodModel_kernel (E := EuclideanSpace ℝ (Fin D.dimension)) Q
  exact he.trans (congrArg (fun S : Subgroup (D.source.comap M.map) =>
    (S : Set (D.source.comap M.map))) (lieQuotientGoodModel_kernel M D))
end DirectedCycles
