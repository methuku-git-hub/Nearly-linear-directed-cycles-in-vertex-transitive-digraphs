module

public import DirectedCycles.NonzeroVectorComplement
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual transverse kernel has dimension exactly one less than the ambient
finite-dimensional real space. -/
theorem vectorComplement_dimension (v : E) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) :
    Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E := by
  have hh := (vectorComplementEquiv v ℓ hℓ).toLinearEquiv.finrank_eq
  simpa only [Module.finrank_prod,Module.finrank_self,add_comm] using hh
end DirectedCycles
