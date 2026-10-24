import DirectedCycles.GleasonGlobalSmoothOperations
import DirectedCycles.LocallyCompactSubgroupTrapping

set_option autoImplicit false
open scoped Manifold ContDiff
namespace DirectedCycles
universe u

/-- An actual compatible Gleason metric yields a finite-dimensional
smooth Lie structure on the supplied topology and group operations. -/
theorem gleason_metric_has_finiteDimensionalLieStructure {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (D : GleasonMetricData G) : HasFiniteDimensionalLieStructure G := by
  obtain ⟨d,⟨e⟩⟩ := GleasonLieAlgebra.exists_euclidean_equiv D
  obtain ⟨r,hr,hreg⟩ := GleasonLieAlgebra.exists_coordinate_smooth_difference_radius D e
  let cs := GleasonLieAlgebra.restrictedCoordinateChartedSpace D e r hr
  refine ⟨d,cs,?_⟩
  let := cs
  let hm : IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ G :=
    GleasonLieAlgebra.restrictedCoordinateChartedSpace_isManifold D e r hr hreg
  exact { toIsManifold := hm
          contMDiff_mul := GleasonLieAlgebra.restrictedCoordinates_contMDiff_mul D e r hr
          contMDiff_inv := GleasonLieAlgebra.restrictedCoordinates_contMDiff_inv D e r hr }

/-- The metric recognition proposition is now discharged, including the
actual smooth atlas, its overlap maps and both global group operations. -/
theorem gleason_metric_lie_recognition : GleasonMetricLieRecognition.{u} := by
  intro G _ _ _ _ _ hD
  obtain ⟨D⟩ := hD
  exact gleason_metric_has_finiteDimensionalLieStructure D

/-- Every locally compact Hausdorff NSS group admits a finite-dimensional
Lie structure compatible with its given topology and operations. -/
theorem locally_compact_nss_lie_recognition : LocallyCompactNSSLieRecognition.{u} :=
  nss_lie_recognition_of_gleason_metric gleason_metric_lie_recognition

/-- The corrected Gleason--Yamabe theorem, with compact approximation,
subgroup trapping and metric-to-Lie recognition all proved. -/
theorem gleason_yamabe_theorem : GleasonYamabeTheorem.{u} :=
  gleason_yamabe_of_nss_lie locally_compact_nss_lie_recognition

end DirectedCycles
