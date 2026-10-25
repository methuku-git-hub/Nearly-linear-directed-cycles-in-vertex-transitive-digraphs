module

public import DirectedCycles.CentralCurveLocalNormal
public import DirectedCycles.OpenSymmetricQuotientWindow

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H]

/-- The actual central segment admits an actual Hausdorff locally compact
local-group quotient. No dimension or Lie smoothness claim is made here. -/
theorem exists_central_curve_topological_quotient (φ : ℝ → H) (hcont : Continuous φ)
    (h0 : φ 0 = 1) (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (h1 : φ 1 ≠ 1)
    (hcentral : ∀ t : ℝ, ∀ x : H, Commute (φ t) x)
    (T : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ T) → x = 1)
    {R : ℝ} (hR : 0 < R) (hbound : ∀ t : ℝ, |t| ≤ R → φ t ∈ T) :
    ∃ V W : Set H, ∃ hP : LocalNormalSet (φ '' Set.Icc (-R) R) V,
      ∃ hW1 : (1 : H) ∈ W, ∃ hWi : W⁻¹ = W, ∃ hW6 : W^6 ⊆ V,
        IsOpen V ∧ IsOpen W ∧ LocalGroupTopology (hP.quotientAlgebra hW1 hWi hW6) ∧
          T2Space (hP.WindowQuotient hW1 hWi hW6) ∧
          LocallyCompactSpace (hP.WindowQuotient hW1 hWi hW6) := by
  obtain ⟨V,hVo,hV1,hP,hPc⟩ := central_nss_curve_locally_normal φ hcont h0 hadd h1 hcentral T hNSS hR hbound
  obtain ⟨W,hWo,hW1,hWi,hW6⟩ := exists_open_symmetric_sixth_subset (hVo.mem_nhds hV1)
  exact ⟨V,W,hP,hW1,hWi,hW6,hVo,hWo,hP.quotientAlgebra_topology hW1 hWi hW6 hWo,
    hP.quotient_t2Space hW1 hWi hW6 hWo (hPc.isClosed.preimage continuous_subtype_val),
    hP.quotient_locallyCompactSpace hW1 hWi hW6 hWo⟩
end DirectedCycles
