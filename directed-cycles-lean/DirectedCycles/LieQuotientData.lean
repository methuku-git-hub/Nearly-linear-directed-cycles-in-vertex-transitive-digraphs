import DirectedCycles.CompactKernelGoodModel
import DirectedCycles.OpenSubgroupGoodModel
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
universe u

/-- The exact geometric output required from Gleason--Yamabe. It records
an open subgroup chosen for this neighbourhood and its actual compact
normal kernel, with an actual finite-dimensional Lie quotient. No existence
of this data is asserted by the definition. -/
structure LieQuotientData (H : Type u) [Group H] [TopologicalSpace H] (V : Set H) where
  source : Subgroup H
  source_open : IsOpen (source : Set H)
  kernel : Subgroup source
  normal : kernel.Normal
  compact_kernel : IsCompact (kernel : Set source)
  kernel_small : (kernel : Set source) ⊆ source.subtype ⁻¹' V
  dimension : ℕ
  charts : ChartedSpace (EuclideanSpace ℝ (Fin dimension)) (source ⧸ kernel)
  lie : let := normal
        let := charts
        LieGroup 𝓘(ℝ,EuclideanSpace ℝ (Fin dimension)) ∞ (source ⧸ kernel)

/-- The precise structural proposition, proved by `gleason_yamabe_theorem`
in `GleasonMetricLieStructure`. Its open subgroup is allowed to depend on
the prescribed identity neighbourhood. -/
def GleasonYamabeTheorem : Prop :=
  ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H],
    ∀ V : Set H, IsOpen V → (1 : H) ∈ V → Nonempty (LieQuotientData H V)

variable {G : Type u} [Group G] {T : Set G} {Internal : Set G → Prop}

/-- Apply specified Lie quotient data to a good model using its actual
source restriction and compact quotient. This does not construct the data. -/
noncomputable def lieQuotientGoodModel
    (M : InternalLocallyCompactGroupModel G T Internal)
    (D : LieQuotientData M.carrier M.neighbourhood) :
    InternalLocallyCompactGroupModel (D.source.comap M.map)
      ((D.source.comap M.map).subtype ⁻¹' T)
      (RestrictedInternal (D.source.comap M.map) Internal) := by
  exact @compactKernelGoodModel (D.source.comap M.map) inferInstance
    ((D.source.comap M.map).subtype ⁻¹' T) (RestrictedInternal (D.source.comap M.map) Internal)
    (openSubgroupGoodModel M D.source D.source_open) D.kernel D.normal
    D.compact_kernel D.kernel_small

theorem lieQuotientGoodModel_map
    (M : InternalLocallyCompactGroupModel G T Internal)
    (D : LieQuotientData M.carrier M.neighbourhood) (x : D.source.comap M.map) :
    let := D.normal
    (lieQuotientGoodModel M D).map x =
      QuotientGroup.mk' D.kernel (subgroupModelHom M.map D.source x) := rfl

theorem lieQuotientGoodModel_lie
    (M : InternalLocallyCompactGroupModel G T Internal)
    (D : LieQuotientData M.carrier M.neighbourhood) :
    let : ChartedSpace (EuclideanSpace ℝ (Fin D.dimension)) (lieQuotientGoodModel M D).carrier :=
      D.charts
    LieGroup 𝓘(ℝ,EuclideanSpace ℝ (Fin D.dimension)) ∞ (lieQuotientGoodModel M D).carrier :=
  D.lie
end DirectedCycles
