import DirectedCycles.FiniteNilpotentLargeModel
import DirectedCycles.FiniteTerminalPeeling
import DirectedCycles.MainFromFiniteAlgebra

set_option autoImplicit false
namespace DirectedCycles

/-- Complete conditional deduction of the manuscript theorem from a single
finite large coset-nilprogression model. The premise is discharged
by finite_nilpotent_large_model in FiniteStructuralTheorems. -/
theorem main_of_finite_large_model (hModel : FiniteNilpotentLargeModel) : MainTheorem :=
  main_of_finite_algebra (finite_classification_of_large_model hModel)
    (finite_nilpotent_envelope_of_abelian_input
      (abelian_short_generation_of_large_model (finite_abelian_large_model_of_nilpotent hModel)))

end DirectedCycles
