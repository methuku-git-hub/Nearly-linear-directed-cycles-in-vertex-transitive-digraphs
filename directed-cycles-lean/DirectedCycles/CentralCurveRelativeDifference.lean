import DirectedCycles.CentralCurveLocalNormal

set_option autoImplicit false
namespace DirectedCycles
variable {H : Type*} [Group H]

/-- Left and right relative differences give the same bounded central-curve
relation, with the order matched to the actual window quotient. -/
theorem central_curve_relative_difference (φ : ℝ → H)
    (hcentral : ∀ t : ℝ, ∀ x : H, Commute (φ t) x) (S : Set ℝ) (x y : H) :
    x*y⁻¹ ∈ φ '' S ↔ y⁻¹*x ∈ φ '' S := by
  constructor
  · rintro ⟨t,ht,he⟩
    refine ⟨t,ht,?_⟩
    calc
      φ t = y⁻¹*(φ t*y) := by rw [(hcentral t y).eq,inv_mul_cancel_left]
      _ = y⁻¹*((x*y⁻¹)*y) := by rw [he]
      _ = y⁻¹*x := by rw [inv_mul_cancel_right]
  · rintro ⟨t,ht,he⟩
    refine ⟨t,ht,?_⟩
    calc
      φ t = (y*φ t)*y⁻¹ := by rw [← (hcentral t y).eq,mul_inv_cancel_right]
      _ = (y*(y⁻¹*x))*y⁻¹ := by rw [he]
      _ = x*y⁻¹ := by rw [mul_inv_cancel_left]
end DirectedCycles
