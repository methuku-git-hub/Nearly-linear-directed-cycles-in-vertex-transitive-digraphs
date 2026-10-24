import DirectedCycles.CentralConnectedModel
import DirectedCycles.ShortProgressionModelEquality
import DirectedCycles.CentralCurveTopologicalQuotient

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- The exact progression image, its nontrivial central curve, and an actual
Hausdorff locally compact local quotient, assembled from the global connected
NSS model. The Lie structure and its dimension drop are still separate. -/
theorem connected_model_central_quotient {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [PreconnectedSpace H] [Nontrivial H] [LocallyCompactSpace H]
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (hA : ∀ᶠ i in (U : Filter ι), (1 : G i) ∈ A i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (u i)^(N i) ∉ A i)
    (hmin : ∀ᶠ i in (U : Filter ι), ∀ v ∈ A i, v ≠ 1 → escapeNorm (A i) (u i) ≤ escapeNorm (A i) v)
    {D : ℝ} (hD : 0 ≤ D)
    (hcomm : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i,
      escapeNorm (A i) (x⁻¹*(u i)⁻¹*x*(u i)) ≤ D*escapeNorm (A i) x*escapeNorm (A i) (u i))
    (π : Subgroup.closure (ultraSet (U : Filter ι) G A) →* H) (hπ : Function.Surjective π)
    (T : Set H) (hT : IsCompact T)
    (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ T) → x = 1)
    (himage : ∀ x : Subgroup.closure (ultraSet (U : Filter ι) G A),
      x.val ∈ ultraSet (U : Filter ι) G A → π x ∈ T)
    (O : Set H) (hOo : IsOpen O) (hO1 : (1 : H) ∈ O)
    (hsmall : ∀ x : Subgroup.closure (ultraSet (U : Filter ι) G A),
      π x ∈ O → x.val ∈ ultraSet (U : Filter ι) G A) :
    ∃ φ : ℝ → H, Continuous φ ∧ φ 0 = 1 ∧
      (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
      (∀ t : ℝ, ∀ x : H, Commute (φ t) x) ∧
      π '' ((Subgroup.closure (ultraSet (U : Filter ι) G A)).subtype ⁻¹'
        ultraSet (U : Filter ι) G (fun i => shortPowerProgression (u i) (N i))) = φ '' Set.Icc (-1 : ℝ) 1 ∧
      ∃ V W : Set H, ∃ hP : LocalNormalSet (φ '' Set.Icc (-1 : ℝ) 1) V,
        ∃ hW1 : (1 : H) ∈ W, ∃ hWi : W⁻¹ = W, ∃ hW6 : W^6 ⊆ V,
          IsOpen V ∧ IsOpen W ∧ LocalGroupTopology (hP.quotientAlgebra hW1 hWi hW6) ∧
            T2Space (hP.WindowQuotient hW1 hWi hW6) ∧
            LocallyCompactSpace (hP.WindowQuotient hW1 hWi hW6) := by
  obtain ⟨φ,hcont,h0,hadd,h1,hformula,hcentral⟩ := connected_model_central_one_parameter U G A u N hA hi
    hprev hexit hmin hD hcomm π hπ T hT hNSS himage O hOo hO1 hsmall
  let B := ultraSet (U : Filter ι) G A
  let S := Subgroup.closure B
  have hsegments : ∀ M : ℕ, ∃ z : GroupUltraproduct (U : Filter ι) G,
      z ≠ 1 ∧ ∀ n ≤ M, z^n ∈ B := by
    intro M
    obtain ⟨z,hz,hp⟩ := exists_long_power_segment_of_connected_model π hπ
      (S.subtype ⁻¹' B) O hOo hO1 hsmall M
    refine ⟨z.val,?_,hp⟩
    exact fun he => hz (Subtype.ext he)
  have hN := minimal_first_escape_unbounded U G A u N hA hprev hexit hmin hsegments
  have heq := shortProgression_model_image_eq U G A u N hN hi hprev S Subgroup.subset_closure π T hNSS himage φ hformula
  have hPA : ultraSet (U : Filter ι) G (fun i => shortPowerProgression (u i) (N i)) ⊆ B := by
    apply ultraSet_mono (U : Filter ι) G
    filter_upwards [hi,hprev] with i hii hpi
    exact shortPowerProgression_subset hii (u i) (N i) hpi
  have hbound : ∀ t : ℝ, |t| ≤ 1 → φ t ∈ T := by
    intro t ht
    have hm : φ t ∈ π '' (S.subtype ⁻¹' ultraSet (U : Filter ι) G (fun i => shortPowerProgression (u i) (N i))) := by
      rw [heq]
      exact ⟨t,abs_le.mp ht,rfl⟩
    obtain ⟨z,hz,he⟩ := hm
    rw [← he]
    exact himage z (hPA hz)
  exact ⟨φ,hcont,h0,hadd,h1,hcentral,heq,
    exists_central_curve_topological_quotient φ hcont h0 hadd h1 hcentral T hNSS (by norm_num) hbound⟩
end DirectedCycles
