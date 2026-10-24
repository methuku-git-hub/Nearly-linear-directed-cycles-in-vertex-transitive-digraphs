import DirectedCycles.GlobalFourthPowerProgressionSequence
import DirectedCycles.UltrafilterModelTransfer

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Pointwise
namespace DirectedCycles

/-- The bounded eventual model principle follows from the constructed Lie
models, complete local dimension induction, NSS reduction and restoration. -/
theorem ultrafilter_coset_model_principle : UltrafilterCosetModelPrinciple := by
  classical
  intro K hK X
  let G := fun i => (X i).carrier
  let : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  let A : ∀ i, Finset (G i) := fun i => (X i).set.toFinset
  have hcoe : ∀ i, (A i : Set (G i)) = (X i).set := fun i => Set.coe_toFinset _
  have hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i)) := by
    intro i
    rw [hcoe]
    exact (X i).approximate
  obtain ⟨r,c,J,_hJ,hP⟩ := global_fourth_power_progression_sequence (Filter.hyperfilter ℕ)
    Nat.hyperfilter_le_atTop G A K hK hA
  refine ⟨r+c+J,?_⟩
  filter_upwards [hP] with i hi
  obtain ⟨P,hPA,hPc⟩ := hi
  refine ⟨r,c,P,by omega,by omega,by simpa only [hcoe] using hPA,?_⟩
  rw [← hcoe i,Nat.card_coe_set_eq,Set.ncard_coe_finset]
  exact hPc.trans (Nat.mul_le_mul_right _ (by omega))

/-- The finite global coset-nilprogression theorem, proved without an
external structure-theorem hypothesis. -/
theorem finite_coset_nilprogression_theorem : FiniteCosetNilprogressionTheorem :=
  finite_coset_input_of_ultrafilter_models ultrafilter_coset_model_principle
end DirectedCycles
