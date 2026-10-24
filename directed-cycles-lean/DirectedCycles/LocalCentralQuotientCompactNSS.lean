import DirectedCycles.LocalCentralQuotientOpenProjection
import DirectedCycles.SmoothLocalCompactNSS
import DirectedCycles.CompactQuotientSourceWindow

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H F : Type*} [TopologicalSpace H] [LocallyCompactSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)
    [ChartedSpace F D.Carrier] [IsManifold 𝓘(ℝ,F) ∞ D.Carrier]

/-- A smooth local quotient has a compact NSS neighbourhood with uniform
finite-power trapping and an actual compact ambient source window mapping
inside it. No global ambient group is needed. -/
theorem exists_compact_nss_source_window (hDo : IsOpen D.small)
    (hD : LocalGroupSmoothness (E := F) D.algebra) (U : Set H) (hU : U ∈ 𝓝 L.one) :
    ∃ V : Set D.Carrier, V ∈ 𝓝 D.algebra.one ∧ IsCompact V ∧
      (∀ x, ∀ p : D.algebra.PowerSequence x, (∀ n, p.power n ∈ V) → x = D.algebra.one) ∧
      (∀ W : Set D.Carrier, W ∈ 𝓝 D.algebra.one → ∃ M : ℕ, 1 ≤ M ∧
        ∀ x, (∀ n ≤ M, D.algebra.PowerIn V x n) → x ∈ W) ∧
      ∃ C : Set H, IsCompact C ∧ L.one ∈ interior C ∧ C ⊆ D.small ∧ C ⊆ U ∧
        ∀ x : D.small, x.val ∈ C → D.project x ∈ V := by
  obtain ⟨V,hV,hVc,_,_,hseq,htrap⟩ := smooth_local_group_compact_nss D.algebra hD
    (Filter.univ_mem : (Set.univ : Set D.Carrier) ∈ 𝓝 D.algebra.one)
  obtain ⟨C,hC,hC1,hCD,hCU,hCV⟩ := compact_quotient_source_window D.small hDo ⟨L.one,D.one_mem⟩
    D.project D.continuous_project hU hV
  exact ⟨V,hV,hVc,hseq,htrap,C,hC,hC1,hCD,hCU,hCV⟩
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
