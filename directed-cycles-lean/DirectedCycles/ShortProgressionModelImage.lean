import DirectedCycles.ScaledExponentLimit
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open scoped Pointwise Topology
namespace DirectedCycles

/-- Bounded normalized exponents have an actual real ultralimit in [-1,1]. -/
theorem short_exponent_has_ultralimit {ι : Type*} (U : Ultrafilter ι)
    (N : ι → ℕ) (k : ι → ℤ)
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hk : ∀ᶠ i in (U : Filter ι), (k i).natAbs < N i) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      Filter.Tendsto (fun i => (k i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t) := by
  let r : ι → ℝ := fun i => (k i : ℝ)/(N i : ℝ)
  have hr : Set.Icc (-1 : ℝ) 1 ∈ Ultrafilter.map r U := by
    change ∀ᶠ i in (U : Filter ι), r i ∈ Set.Icc (-1 : ℝ) 1
    filter_upwards [hN,hk] with i hNi hki
    have hNr : (0 : ℝ) < N i := by exact_mod_cast hNi
    have hb := (int_natAbs_lt_iff (k i) (N i)).1 hki
    have hlo : -(N i : ℝ) < (k i : ℝ) := by exact_mod_cast hb.1
    have hhi : (k i : ℝ) < (N i : ℝ) := by exact_mod_cast hb.2
    constructor
    · apply (le_div_iff₀ hNr).2
      linarith
    · apply (div_le_iff₀ hNr).2
      linarith
  obtain ⟨t,ht,hlim⟩ := isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map r U) hr
  refine ⟨t,ht,?_⟩
  change Filter.map r (U : Filter ι) ≤ 𝓝 t
  simpa only [Ultrafilter.coe_map] using hlim

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- Every element of the actual internal first-exit progression maps to the
closed unit segment of the constructed curve. The real parameter is obtained
from compactness, and equality is obtained from the proved NSS kernel lemma. -/
theorem shortProgression_model_image {H : Type*} [Group H]
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (S : Subgroup (GroupUltraproduct (U : Filter ι) G)) (π : S →* H)
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z : S, z.val ∈ ultraSet (U : Filter ι) G A → π z ∈ V)
    (φ : ℝ → H)
    (hφ : ∀ t : ℝ, ∃ h : scaledUltraPower U G u N t ∈ S,
      φ t = π ⟨scaledUltraPower U G u N t,h⟩)
    (z : S) (hz : z.val ∈ ultraSet (U : Filter ι) G (fun i => shortPowerProgression (u i) (N i))) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1, π z = φ t := by
  classical
  obtain ⟨v,hv⟩ := ultraMk_surjective (U : Filter ι) G z.val
  have hvm : ∀ᶠ i in (U : Filter ι), v i ∈ shortPowerProgression (u i) (N i) :=
    (ultraMk_mem_ultraSet_iff _ G _ v).1 (hv.symm ▸ hz)
  have hc : ∀ i, ∃ k : ℤ, v i ∈ shortPowerProgression (u i) (N i) →
      k.natAbs < N i ∧ (u i)^k = v i := by
    intro i
    by_cases h : v i ∈ shortPowerProgression (u i) (N i)
    · obtain ⟨k,hk,he⟩ := h
      exact ⟨k,fun _ => ⟨hk,he⟩⟩
    · exact ⟨0,fun hh => (h hh).elim⟩
  choose k hk using hc
  have hkN : ∀ᶠ i in (U : Filter ι), (k i).natAbs < N i := hvm.mono fun i hi => (hk i hi).1
  have he : ultraMk (U : Filter ι) G (fun i => (u i)^(k i)) = z.val := by
    rw [← hv]
    apply (ultraMk_eq_iff _ G _ _).2
    exact hvm.mono fun i hi => (hk i hi).2
  obtain ⟨t,ht,hlim⟩ := short_exponent_has_ultralimit U N k (hN 0) hkN
  obtain ⟨htS,hft⟩ := hφ t
  have hkS : ultraMk (U : Filter ι) G (fun i => (u i)^(k i)) ∈ S := he.symm ▸ z.property
  have hm := model_scaled_exponent_limit U G A u N k t hN hi hprev hlim S π V hNSS himage hkS htS
  have hsub : (⟨ultraMk (U : Filter ι) G (fun i => (u i)^(k i)),hkS⟩ : S) = z := Subtype.ext he
  exact ⟨t,ht,by simpa only [hsub,← hft] using hm⟩
end DirectedCycles
