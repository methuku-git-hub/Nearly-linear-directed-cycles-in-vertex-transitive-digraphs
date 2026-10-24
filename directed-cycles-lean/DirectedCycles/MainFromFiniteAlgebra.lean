import DirectedCycles.MainFromStructure
import DirectedCycles.FiniteTriplingFromAlgebra
import DirectedCycles.FiniteBGTCorollary
import DirectedCycles.FiniteEnvelopeReduction

set_option autoImplicit false
namespace DirectedCycles

/-- The remaining two finite algebra inputs are explicit premises, not axioms.
This is a conditional reduction and is not the manuscript's main theorem. -/
theorem main_of_finite_algebra (hClass : FiniteApproximateClassification)
    (hEnvelope : FiniteNilpotentEnvelope) : MainTheorem :=
  main_of_finite_structure (finite_structure_of_tripling
    (finite_tripling_from_algebra (finite_structure_from_classification hClass)
      (finite_envelope_of_nilpotent hEnvelope)))

end DirectedCycles
