import DirectedCycles.LieOneParameterProductCoordinates
import DirectedCycles.CentralCurveSliceRelation
import DirectedCycles.CentralCurveRelativeDifference
import DirectedCycles.LocalSliceQuotientManifold

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- The actual quotient by a bounded central curve segment has a constructed
smooth manifold atlas of dimension one less. This proves the manifold and
relation part of dimension reduction; smoothness of the partial group operations
is not included in this theorem. -/
theorem exists_lie_central_quotient_manifold (φ : ℝ → H) (hcont : Continuous φ)
    (h0 : φ 0 = 1) (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (h1 : φ 1 ≠ 1)
    (hcentral : ∀ t : ℝ, ∀ x : H, Commute (φ t) x)
    (T : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ T) → x = 1)
    {R : ℝ} (hR : 0 < R) (hbound : ∀ t : ℝ, |t| ≤ R → φ t ∈ T) :
    ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
      Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E ∧
      ∃ V W : Set H, ∃ hP : LocalNormalSet (φ '' Set.Icc (-R) R) V,
        ∃ hW1 : (1 : H) ∈ W, ∃ hWi : W⁻¹ = W, ∃ hW6 : W^6 ⊆ V,
          IsOpen V ∧ IsOpen W ∧
          ∃ a : OpenPartialHomeomorph (ℝ × ℓ.ker) H,
            (0 : ℝ × ℓ.ker) ∈ a.source ∧ a 0 = 1 ∧ W ⊆ a.target ∧
            (∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ φ '' Set.Icc (-R) R ↔ (a.symm x).2 = (a.symm y).2) ∧
            ∃ cs : ChartedSpace ℓ.ker (hP.WindowQuotient hW1 hWi hW6),
              @IsManifold ℝ _ ℓ.ker _ _ ℓ.ker _ 𝓘(ℝ,ℓ.ker) ∞
                (hP.WindowQuotient hW1 hWi hW6) _ cs := by
  obtain ⟨v,ℓ,hv,hℓ,hdim,a,ha0,ha1,hformula⟩ :=
    lieGroup_one_parameter_product_coordinates (E := E) φ h0 hcont.continuousAt hadd ⟨1,h1⟩
  have hgap : ∀ t : ℝ, 0 < |t| → |t| ≤ 2*R → φ t ≠ 1 :=
    fun t ht hb => real_curve_kernel_gap φ h0 hadd h1 T hNSS R hbound ht hb
  obtain ⟨W₀,hW₀o,hW₀1,_,hW₀a,hrel₀⟩ := central_curve_slice_relation φ hcont hadd hcentral hR
    (fun t ht hb => hgap t ht (by linarith)) a ha0 ha1
    (fun z => (chartAt E (1 : H)).symm ((z : E)+(chartAt E (1 : H)) 1)) hformula
  obtain ⟨V,hVo,hV1,hP,_⟩ := central_curve_locally_normal φ hcont h0 hadd hcentral hR hgap
  obtain ⟨W,hWo,hW1,hWi,hW6'⟩ := exists_open_symmetric_sixth_subset
    ((hVo.inter hW₀o).mem_nhds ⟨hV1,hW₀1⟩)
  have hW6 : W^6 ⊆ V := fun x hx => (hW6' hx).1
  have hWW₀ : W ⊆ W₀ := by
    intro x hx
    have hh : x ∈ W^1 := by simpa only [pow_one] using hx
    exact (hW6' ((Set.pow_subset_pow_right hW1 (by omega : 1 ≤ 6)) hh)).2
  have hWa : W ⊆ a.target := hWW₀.trans hW₀a
  have hrel : ∀ x ∈ W, ∀ y ∈ W,
      x*y⁻¹ ∈ φ '' Set.Icc (-R) R ↔ (a.symm x).2 = (a.symm y).2 := by
    intro x hx y hy
    rw [central_curve_relative_difference φ hcentral (Set.Icc (-R) R) x y]
    exact (hrel₀ y (hWW₀ hy) x (hWW₀ hx)).trans eq_comm
  let cs := (hP.sliceChart hW1 hWi hW6 a hWo hWa hrel).singletonChartedSpace
    (hP.sliceChart_source hW1 hWi hW6 a hWo hWa hrel)
  exact ⟨v,ℓ,hv,hℓ,hdim,V,W,hP,hW1,hWi,hW6,hVo,hWo,a,ha0,ha1,hWa,hrel,cs,
    hP.sliceChart_isManifold hW1 hWi hW6 a hWo hWa hrel⟩
end DirectedCycles
