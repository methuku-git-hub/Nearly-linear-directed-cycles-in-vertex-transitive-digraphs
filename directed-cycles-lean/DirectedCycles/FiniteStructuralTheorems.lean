import DirectedCycles.FiniteCosetNilprogressionTheorem
import DirectedCycles.MainFromLargeModel
import DirectedCycles.FiniteCosetNilprogressionInput

set_option autoImplicit false
namespace DirectedCycles

/-- Unconditional finite contained-model consequence of the proved structure theorem. -/
theorem finite_nilpotent_large_model : FiniteNilpotentLargeModel :=
  finite_large_model_of_coset_nilprogression finite_coset_nilprogression_theorem

theorem finite_approximate_classification : FiniteApproximateClassification :=
  finite_classification_of_large_model finite_nilpotent_large_model

theorem finite_abelian_large_model : FiniteAbelianLargeModel :=
  finite_abelian_large_model_of_nilpotent finite_nilpotent_large_model

theorem finite_abelian_short_generation : FiniteAbelianShortGeneration :=
  abelian_short_generation_of_large_model finite_abelian_large_model

theorem finite_terminal_peeling : FiniteTerminalPeeling :=
  finite_terminal_peeling_of_abelian_input finite_abelian_short_generation

theorem finite_nilpotent_envelope : FiniteNilpotentEnvelope :=
  finite_nilpotent_envelope_of_abelian_input finite_abelian_short_generation

theorem finite_approximate_structure : FiniteApproximateStructure :=
  finite_structure_from_classification finite_approximate_classification

theorem finite_normal_envelope : FiniteNormalEnvelope :=
  finite_envelope_of_nilpotent finite_nilpotent_envelope

theorem finite_tripling_structure : FiniteTriplingStructure :=
  finite_tripling_from_algebra finite_approximate_structure finite_normal_envelope

/-- The finite graph structural consequence needed for manuscript Theorem 1.5.
The permutation group is the actual induced group on the normal orbits. -/
theorem finite_structural_input : FiniteStructuralInput :=
  finite_structure_of_tripling finite_tripling_structure
end DirectedCycles
