import DirectedCycles.FiniteStructuralTheorems
import DirectedCycles.MainFromCosetNilprogression

set_option autoImplicit false
namespace DirectedCycles

/-- Manuscript Theorem 1.5, through the proved finite structural theorem
and the checked directed-graph deduction. -/
theorem theorem_1_5 : MainTheorem :=
  main_of_finite_structure finite_structural_input
end DirectedCycles
