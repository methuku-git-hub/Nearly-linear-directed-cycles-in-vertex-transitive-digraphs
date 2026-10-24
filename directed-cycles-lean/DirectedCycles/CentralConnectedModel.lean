import DirectedCycles.ConnectedScaledModel
import DirectedCycles.ScaledCurveCentrality
import DirectedCycles.UniformCentralEscape
import DirectedCycles.ModelEscapeNeighbourhood

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- A connected global NSS model of least-escape elements produces a genuine
nontrivial central continuous one-parameter subgroup. Both the unbounded
scales and the model neighbourhood centralized by the curve are derived. -/
theorem connected_model_central_one_parameter {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [PreconnectedSpace H] [Nontrivial H]
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
    (V : Set H) (hV : IsCompact V)
    (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ x : Subgroup.closure (ultraSet (U : Filter ι) G A),
      x.val ∈ ultraSet (U : Filter ι) G A → π x ∈ V)
    (W : Set H) (hWo : IsOpen W) (hW1 : (1 : H) ∈ W)
    (hsmall : ∀ x : Subgroup.closure (ultraSet (U : Filter ι) G A),
      π x ∈ W → x.val ∈ ultraSet (U : Filter ι) G A) :
    ∃ φ : ℝ → H, Continuous φ ∧ φ 0 = 1 ∧
      (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
      (∀ t : ℝ, ∃ h : scaledUltraPower U G u N t ∈ Subgroup.closure (ultraSet (U : Filter ι) G A),
        φ t = π ⟨scaledUltraPower U G u N t,h⟩) ∧
      (∀ t : ℝ, ∀ x : H, Commute (φ t) x) := by
  obtain ⟨φ,hcont,h0,hadd,h1,hformula⟩ := connected_model_one_parameter U G A u N hA hi hprev
    hexit hmin π hπ V hV hNSS himage W hWo hW1 hsmall
  refine ⟨φ,hcont,h0,hadd,h1,hformula,?_⟩
  let C : ∀ i, Set (G i) := fun i => escapeSublevel (A i) (centralizingEscapeRadius D)
  have hcentral : ∀ᶠ i in (U : Filter ι), ∀ v ∈ C i, Commute (u i) v := by
    filter_upwards [hA,hexit,hcomm,hmin] with i hAi hexi hci hmi
    have hNi : 0 < N i := by
      by_contra hn
      have he : N i = 0 := by omega
      exact hexi (by simpa [he] using hAi)
    have huPos : 0 < escapeNorm (A i) (u i) :=
      lt_of_lt_of_le (by positivity) (inv_le_escapeNorm_of_not_mem hAi hexi)
    intro v hv
    exact (centralizes_of_escapeNorm_le_radius hAi huPos hmi hD hci hv).symm
  obtain ⟨O,hOo,hO1,hOsmall⟩ := model_escapeSublevel_neighbourhood U G A _ π W hWo hW1 hsmall
    (centralizingEscapeRadius_pos hD)
  apply scaled_curve_central U G u N C _ π φ hformula hcentral O (hOo.mem_nhds hO1)
  intro x hx
  obtain ⟨z,hz⟩ := hπ x
  exact ⟨z,hOsmall z (hz.symm ▸ hx),hz⟩
end DirectedCycles
