import DirectedCycles.FiniteCosetNilprogressionInput
import DirectedCycles.MainFromLargeModel

set_option autoImplicit false
namespace DirectedCycles

/-- Deduction from the finite global structure statement. The unconditional
statement is proved in FiniteCosetNilprogressionTheorem; the final manuscript
theorem is theorem_1_5. -/
theorem main_of_finite_coset_nilprogression (hBGT : FiniteCosetNilprogressionTheorem) : MainTheorem :=
  main_of_finite_large_model (finite_large_model_of_coset_nilprogression hBGT)

end DirectedCycles
