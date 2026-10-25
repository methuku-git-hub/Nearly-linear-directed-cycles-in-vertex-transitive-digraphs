module

public import DirectedCycles.SmoothLocalCurveProductCoordinates
public import DirectedCycles.SmoothLocalCurveNonzeroTangent
public import DirectedCycles.LocalCurveKernelGap
public import DirectedCycles.LocalCurveSliceRelation
public import DirectedCycles.LocalCentralQuotientNeighbourhood
public import DirectedCycles.LocalCentralQuotientSmoothness
public import DirectedCycles.LocalCentralQuotientSliceTopology

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]

/-- A specified central curve segment in an actual smooth local group has an
actual smooth local quotient of dimension one less. Product domains, the
bounded-segment equivalence, topology and smooth operations are all proved. -/
theorem exists_smooth_local_central_quotient (Q : LocalGroupAlgebra H)
    (hQ : LocalGroupSmoothness (E := E) Q) (hd : Q.DivisionClosed) (hr : Q.Reversible)
    (f : ℝ → H) (hf0 : f 0 = Q.one) (hfc : ContinuousAt f 0)
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    (hf1 : f 1 ≠ Q.one) (A : Set H)
    (hNSS : ∀ x : H, ∀ p : Q.PowerSequence x, (∀ n, p.power n ∈ A) → x = Q.one)
    (hbound : ∀ t : ℝ, |t| ≤ 1 → f t ∈ A)
    (hdom : ∀ s t : ℝ, |s| ≤ 1 → |t| ≤ 1 → Q.Defined (f s) (f t))
    (V S : Set H) (hV : V ∈ 𝓝 Q.one) (hS : S ∈ 𝓝 Q.one)
    (hP : Q.CentralLocalSet (f '' Set.Icc (-1 : ℝ) 1) V S) :
    ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
      Module.finrank ℝ ℓ.ker+1 = Module.finrank ℝ E ∧
      ∃ T : Q.CentralQuotientData (f '' Set.Icc (-1 : ℝ) 1), IsOpen T.small ∧
        T.algebra.DivisionClosed ∧ T.algebra.Reversible ∧
        T2Space T.Carrier ∧ LocallyCompactSpace T.Carrier ∧
        ∃ a : OpenPartialHomeomorph (ℝ × ℓ.ker) H, (0 : ℝ × ℓ.ker) ∈ a.source ∧
          a 0 = Q.one ∧ T.small ⊆ a.target ∧
          (∀ x y : T.small, T.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) ∧
          ∃ cs : ChartedSpace ℓ.ker T.Carrier,
            letI := cs
            IsManifold 𝓘(ℝ,ℓ.ker) ∞ T.Carrier ∧ LocalGroupSmoothness (E := ℓ.ker) T.algebra := by
  obtain ⟨D⟩ := smooth_local_exponential_data Q hQ
  obtain ⟨v,ℓ,hv,hℓ,hdim,a,σ,ha0,ha1,_,haSmooth,haInv,hformula⟩ :=
    smooth_local_curve_product_coordinates Q hQ f hf0 hfc hadd hf1
  have hfs := (smooth_local_curve_nonzero_tangent Q hQ f hf0 hfc hadd hf1).1
  have hcont := smooth_local_curve_continuousOn_segment Q hQ f hf0 hfs hadd
  have hgap : ∀ t : ℝ, 0 < |t| → |t| ≤ 1 → f t ≠ Q.one :=
    fun _ ht ht1 => local_curve_kernel_gap Q hr f hf0 hadd hf1 A hNSS hbound hdom ht ht1
  obtain ⟨W,hWo,hW1,_,hWa,hrel⟩ := local_curve_slice_relation D hd f hf0 hfc hcont hadd hgap a ha0 ha1 σ hformula
  obtain ⟨T,hTo,hTW⟩ := local_central_quotient_of_neighbourhoods D hd hr hP hV hS W (hWo.mem_nhds hW1)
  have hTa : T.small ⊆ a.target := hTW.trans hWa
  have hTrel : ∀ x y : T.small, T.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2 := by
    intro x y
    exact (T.relation_iff x y).trans (hrel x.val (hTW x.property) y.val (hTW y.property))
  let cs := T.sliceChartedSpace a hTo hTa hTrel
  obtain ⟨hT2,hTlc⟩ := T.slice_topology a hTo hTa hTrel
  exact ⟨v,ℓ,hv,hℓ,hdim,T,hTo,T.algebra_divisionClosed hd,T.algebra_reversible hr,hT2,hTlc,
    a,ha0,ha1,hTa,hTrel,cs,T.sliceChartedSpace_isManifold a hTo hTa hTrel,
    T.algebra_smooth a hTo hTa hTrel hQ haSmooth haInv⟩
end DirectedCycles
