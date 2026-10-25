module

public import DirectedCycles.ConnectedSmallPowers
public import DirectedCycles.MinimalEscapeUnbounded
public import DirectedCycles.ScaledPowerModel

@[expose] public section

set_option autoImplicit false
open scoped Pointwise Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- The nontrivial continuous one-parameter construction for a connected global
model. Unbounded scales are deduced from minimal escape and connectedness,
rather than added as a hypothesis. -/
theorem connected_model_one_parameter {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [PreconnectedSpace H] [Nontrivial H]
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (hA : ∀ᶠ i in (U : Filter ι), (1 : G i) ∈ A i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (u i)^(N i) ∉ A i)
    (hmin : ∀ᶠ i in (U : Filter ι), ∀ v ∈ A i, v ≠ 1 → escapeNorm (A i) (u i) ≤ escapeNorm (A i) v)
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
        φ t = π ⟨scaledUltraPower U G u N t,h⟩) := by
  let B := ultraSet (U : Filter ι) G A
  let S := Subgroup.closure B
  have hsegments : ∀ M : ℕ, ∃ z : GroupUltraproduct (U : Filter ι) G,
      z ≠ 1 ∧ ∀ n ≤ M, z^n ∈ B := by
    intro M
    obtain ⟨z,hz,hp⟩ := exists_long_power_segment_of_connected_model π hπ
      (S.subtype ⁻¹' B) W hWo hW1 hsmall M
    refine ⟨z.val,?_,?_⟩
    · intro he
      exact hz (Subtype.ext he)
    · exact hp
  have hN := minimal_first_escape_unbounded U G A u N hA hprev hexit hmin hsegments
  exact exists_scaled_one_parameter U G A u N hN hi hprev hexit π V hV hNSS himage W hW1 hsmall
end DirectedCycles
