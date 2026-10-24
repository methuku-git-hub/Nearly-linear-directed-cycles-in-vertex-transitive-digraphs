import DirectedCycles.RegularizedEscapeDistance

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

theorem regularizedEscapeDistance_le_word {A : Set G} (hA : 1 ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) (l : List G) :
    regularizedEscapeDistance A ε l.prod ≤
      (l.map (escapeNorm A)).sum + (l.length : ℝ)*ε := by
  have hw : ∀ g, 0 ≤ escapeNorm A g + ε := fun g => add_nonneg (escapeNorm_nonneg hA g) hε
  have he : (l.map (fun g => escapeNorm A g + ε)).sum =
      (l.map (escapeNorm A)).sum + (l.length : ℝ)*ε := by
    induction l with
    | nil => simp
    | cons g l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]; ring
  exact (wordNorm_le_cost hw l).trans_eq he

/-- Uniform control of the actual regularized distances implies the unregularized
product inequality for every finite word. -/
theorem escape_product_bound_of_regularized {A : Set G} (hA : 1 ∈ A)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ∀ g : G, escapeNorm A g ≤ C*regularizedEscapeDistance A ε g)
    (l : List G) : escapeNorm A l.prod ≤ C*(l.map (escapeNorm A)).sum := by
  apply le_of_forall_pos_le_add
  intro η hη
  let t := C*(l.length : ℝ)+1
  have ht : 0 < t := by dsimp [t]; positivity
  let ε := η/t
  have hε : 0 < ε := div_pos hη ht
  have hh := (h ε hε l.prod).trans (mul_le_mul_of_nonneg_left
    (regularizedEscapeDistance_le_word hA hε.le l) hC)
  have he : t*ε = η := by dsimp [ε]; field_simp
  have herror : C*(l.length : ℝ)*ε ≤ η := by
    have htC : C*(l.length : ℝ) ≤ t := by dsimp [t]; linarith
    exact (mul_le_mul_of_nonneg_right htC hε.le).trans_eq he
  nlinarith
end DirectedCycles
