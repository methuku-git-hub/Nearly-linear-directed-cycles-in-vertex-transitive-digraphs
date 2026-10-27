module

public import DirectedCycles.FiniteApproximateCounterexamples
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- The bounded eventual-model conclusion that an ultraproduct structure
proof supplies via ultrafilter_coset_model_principle. -/
def UltrafilterCosetModelPrinciple : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∀ X : ℕ → FiniteApproximateExample K,
    ∃ n : ℕ, ∀ᶠ i in (Filter.hyperfilter ℕ : Filter ℕ),
      HasCosetNilprogressionModel (X i).set n

/-- Formal finite deduction from bounded eventual models. Producing those
models is supplied by ultrafilter_coset_model_principle. -/
theorem finite_coset_input_of_ultrafilter_models (hUltra : UltrafilterCosetModelPrinciple) :
    FiniteCosetNilprogressionTheorem := by
  classical
  by_contra hnot
  obtain ⟨K,hK,X,hfail,_hcard⟩ := finite_coset_counterexample_sequence hnot
  obtain ⟨n,hn⟩ := hUltra K hK X
  have hlarge : ∀ᶠ i in (Filter.hyperfilter ℕ : Filter ℕ), n ≤ i+1 := by
    have h : ∀ᶠ i in (Filter.hyperfilter ℕ : Filter ℕ), n ≤ i :=
      (eventually_ge_atTop n).filter_mono Nat.hyperfilter_le_atTop
    exact h.mono (fun i hi => by omega)
  obtain ⟨i,hi,hni⟩ := (hn.and hlarge).exists
  exact hfail i (hi.mono hni)

theorem ultrafilter_models_of_finite_coset_input (hFinite : FiniteCosetNilprogressionTheorem) :
    UltrafilterCosetModelPrinciple := by
  intro K hK X
  obtain ⟨n,_hn,hmodel⟩ := finite_coset_input_iff_examples.mp hFinite K hK
  exact ⟨n,Eventually.of_forall (fun i => hmodel (X i))⟩

end DirectedCycles
