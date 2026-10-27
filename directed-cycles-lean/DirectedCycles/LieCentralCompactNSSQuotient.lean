module

public import DirectedCycles.LieCentralSmoothQuotient
public import DirectedCycles.SmoothLocalCompactNSS
public import DirectedCycles.LocalQuotientSeparation
public import DirectedCycles.CompactQuotientSourceWindow

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- The constructed central Lie quotient includes its lower-dimensional
smooth structure, Hausdorff topology, compact NSS target and a compact source
neighbourhood inside the original model neighbourhood. -/
theorem exists_lie_central_compact_nss_quotient (φ : ℝ → H) (hcont : Continuous φ)
    (h0 : φ 0 = 1) (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (h1 : φ 1 ≠ 1)
    (hcentral : ∀ t : ℝ, ∀ x : H, Commute (φ t) x)
    (T : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ T) → x = 1)
    (hbound : ∀ t : ℝ, |t| ≤ 1 → φ t ∈ T)
    (U₀ : Set H) (hU₀ : U₀ ∈ 𝓝 (1 : H)) :
    ∃ (v : E) (ℓ : E →L[ℝ] ℝ), v ≠ 0 ∧ ℓ v = 1 ∧
      Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E ∧
      ∃ V W : Set H, ∃ hQ : LocalNormalSet (φ '' Set.Icc (-1 : ℝ) 1) V,
        ∃ hW1 : (1 : H) ∈ W, ∃ hWi : W⁻¹ = W, ∃ hW6 : W^6 ⊆ V,
          IsOpen W ∧ T2Space (hQ.WindowQuotient hW1 hWi hW6) ∧
          ∃ cs : ChartedSpace ℓ.ker (hQ.WindowQuotient hW1 hWi hW6),
            let := cs
            IsManifold 𝓘(ℝ,ℓ.ker) ∞ (hQ.WindowQuotient hW1 hWi hW6) ∧
            LocalGroupSmoothness (E := ℓ.ker) (hQ.quotientAlgebra hW1 hWi hW6) ∧
            ∃ Vq : Set (hQ.WindowQuotient hW1 hWi hW6),
              Vq ∈ 𝓝 (hQ.quotientAlgebra hW1 hWi hW6).one ∧ IsCompact Vq ∧
              (∀ x, ∀ p : (hQ.quotientAlgebra hW1 hWi hW6).PowerSequence x,
                (∀ n, p.power n ∈ Vq) → x = (hQ.quotientAlgebra hW1 hWi hW6).one) ∧
              ∃ C : Set H, IsCompact C ∧ (1 : H) ∈ interior C ∧ C ⊆ W ∧ C ⊆ U₀ ∧
                ∀ x : W, x.val ∈ C → hQ.windowMk hW1 hWi hW6 x ∈ Vq := by
  let : LocallyCompactSpace H := Manifold.locallyCompact_of_finiteDimensional 𝓘(ℝ,E)
  obtain ⟨v,ℓ,hv,hℓ,hdim,V,W,hQ,hW1,hWi,hW6,_,hWo,_,_,_,_,_,cs,hman,hsmooth⟩ :=
    exists_lie_central_smooth_quotient (E := E) φ hcont h0 hadd h1 hcentral T hNSS (by norm_num) hbound
  let := cs
  let := hman
  have hQclosed : IsClosed (Subtype.val ⁻¹' (φ '' Set.Icc (-1 : ℝ) 1) : Set V) :=
    (isCompact_Icc.image hcont).isClosed.preimage continuous_subtype_val
  have hT2 := hQ.quotient_t2Space hW1 hWi hW6 hWo hQclosed
  obtain ⟨Vq,hVq,hVqc,_,_,hseq,_⟩ := smooth_local_group_compact_nss (hQ.quotientAlgebra hW1 hWi hW6)
    hsmooth (Filter.univ_mem : (Set.univ : Set (hQ.WindowQuotient hW1 hWi hW6)) ∈ 𝓝 _)
  obtain ⟨C,hC,hC1,hCW,hCU,hCV⟩ := compact_quotient_source_window W hWo ⟨1,hW1⟩
    (hQ.windowMk hW1 hWi hW6) (hQ.continuous_windowMk hW1 hWi hW6) hU₀ hVq
  exact ⟨v,ℓ,hv,hℓ,hdim,V,W,hQ,hW1,hWi,hW6,hWo,hT2,cs,hman,hsmooth,Vq,hVq,hVqc,hseq,C,hC,hC1,hCW,hCU,hCV⟩
end DirectedCycles
