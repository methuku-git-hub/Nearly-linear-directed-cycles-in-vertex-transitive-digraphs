import DirectedCycles.LocalDivision
import DirectedCycles.FiniteGroupDerivatives

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Translation by a local group element, extended by zero outside its actual
range. No arbitrary multiplication is introduced at undefined pairs. -/
noncomputable def leftShift (g : G) (f : G → ℝ) (x : G) : ℝ := by
  classical
  exact if h : ∃ y, L.mulRel g y x then f (Classical.choose h) else 0

theorem leftShift_of_mulRel (hL : L.Cancellative) {g y x : G}
    (hm : L.mulRel g y x) (f : G → ℝ) : L.leftShift g f x = f y := by
  classical
  unfold leftShift
  rw [dite_eq_left ⟨y,hm⟩]
  exact congrArg f (hL.left_cancel (Classical.choose_spec (show ∃ y, L.mulRel g y x from ⟨y,hm⟩)) hm)

theorem leftShift_of_no_preimage {g x : G} (h : ¬ ∃ y, L.mulRel g y x) (f : G → ℝ) :
    L.leftShift g f x = 0 := by
  classical
  exact dite_eq_right h

theorem leftShift_one (hL : L.Cancellative) (f : G → ℝ) : L.leftShift L.one f = f := by
  funext x
  exact L.leftShift_of_mulRel hL (L.one_mul x) f

/-- A local translation is linear even though it is only partially defined. -/
theorem leftShift_sub (g : G) (f k : G → ℝ) :
    L.leftShift g (f-k) = L.leftShift g f-L.leftShift g k := by
  classical
  funext x
  simp only [leftShift,Pi.sub_apply]
  split_ifs <;> simp

/-- Inverse translation cancels on functions whose support lies in the
forward translation domain. This support premise is essential locally. -/
theorem leftShift_inv_leftShift (hd : L.DivisionClosed) (hr : L.Reversible)
    (g : G) (f : G → ℝ) (hs : ∀ x, f x ≠ 0 → L.Defined g x) :
    L.leftShift (L.inv g) (L.leftShift g f) = f := by
  classical
  have hc := hd.cancellative L hr
  funext x
  by_cases h : ∃ y, L.mulRel (L.inv g) y x
  · obtain ⟨y,hy⟩ := h
    rw [L.leftShift_of_mulRel hc hy]
    have hm : L.mulRel g x y := by simpa only [L.inv_inv] using hd.left hy
    exact L.leftShift_of_mulRel hc hm f
  · rw [L.leftShift_of_no_preimage h]
    by_contra hx
    have hx' : f x ≠ 0 := fun he => hx he.symm
    obtain ⟨y,hy⟩ := hs x hx'
    exact h ⟨y,hd.left hy⟩

noncomputable def derivative (g : G) (f : G → ℝ) : G → ℝ := L.leftShift g f-f

section Finite
variable [Fintype G]

/-- Zero-extended partial translations are contractions. -/
theorem norm_leftShift_le (g : G) (f : G → ℝ) : ‖L.leftShift g f‖ ≤ ‖f‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2
  intro x
  unfold leftShift
  split_ifs
  · exact norm_le_pi_norm f _
  · simp only [norm_zero]
    exact norm_nonneg f

/-- Translation is an isometry on functions supported in its actual domain. -/
theorem norm_leftShift_eq (hL : L.Cancellative) (g : G) (f : G → ℝ)
    (hs : ∀ x, f x ≠ 0 → L.Defined g x) : ‖L.leftShift g f‖ = ‖f‖ := by
  apply le_antisymm (L.norm_leftShift_le g f)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (L.leftShift g f))).2
  intro y
  by_cases hy : f y = 0
  · rw [hy,norm_zero]
    exact norm_nonneg _
  · obtain ⟨x,hx⟩ := hs y hy
    have hb := norm_le_pi_norm (L.leftShift g f) x
    rw [L.leftShift_of_mulRel hL hx] at hb
    exact hb

noncomputable def derivativeNorm (f : G → ℝ) (g : G) : ℝ := ‖L.derivative g f‖

theorem derivativeNorm_le_two_mul (f : G → ℝ) (g : G) :
    L.derivativeNorm f g ≤ 2*‖f‖ := by
  unfold derivativeNorm derivative
  calc
    ‖L.leftShift g f-f‖ ≤ ‖L.leftShift g f‖+‖f‖ := norm_sub_le _ _
    _ ≤ ‖f‖+‖f‖ := add_le_add (L.norm_leftShift_le g f) le_rfl
    _ = 2*‖f‖ := by ring

theorem abs_derivative_le (f : G → ℝ) (g x : G) :
    |L.derivative g f x| ≤ L.derivativeNorm f g := by
  simpa only [derivativeNorm,Real.norm_eq_abs] using norm_le_pi_norm (L.derivative g f) x
end Finite
end LocalGroupAlgebra
end DirectedCycles
