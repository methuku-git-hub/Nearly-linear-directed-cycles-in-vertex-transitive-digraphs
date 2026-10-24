import DirectedCycles.BoundedGroupDerivative

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The commutator translated difference is bounded by the two actual
mixed second differences, without a finite-domain function norm. -/
theorem boundedDerivative_commutator_bound {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g h : G) {A B : ℝ}
    (hgh : ∀ x, |groupDerivative g (groupDerivative h f) x| ≤ A)
    (hhg : ∀ x, |groupDerivative h (groupDerivative g f) x| ≤ B) :
    boundedDerivative f (g⁻¹*h⁻¹*g*h) ≤ A+B := by
  apply (boundedDerivative_le_iff hf _ _).2
  intro x
  have he := congrFun (groupDerivative_commutator_identity g h f) ((h*g)*x)
  change groupDerivative (g⁻¹*h⁻¹*g*h) f ((h*g)⁻¹*((h*g)*x)) = _ at he
  rw [inv_mul_cancel_left] at he
  rw [he]
  exact (abs_sub _ _).trans (add_le_add (hgh _) (hhg _))
end DirectedCycles
