module

public import DirectedCycles.ShortProgressionProperness
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A canonical exponent strictly inside the first-exit progression. -/
noncomputable def clampedScaledExponent (t : ℝ) (N : ℕ) : ℤ :=
  max (-(N : ℤ)+1) (min ((N : ℤ)-1) (Int.floor (t*(N : ℝ))))

theorem clampedScaledExponent_natAbs_lt (t : ℝ) {N : ℕ} (hN : 0 < N) :
    (clampedScaledExponent t N).natAbs < N := by
  apply (int_natAbs_lt_iff _ _).2
  have hNr : (0 : ℤ) < N := by exact_mod_cast hN
  unfold clampedScaledExponent
  constructor
  · exact lt_of_lt_of_le (by omega) (le_max_left _ _)
  · apply max_lt
    · omega
    · exact lt_of_le_of_lt (min_le_left _ _) (by omega)

/-- On the closed unit interval, clamping changes the floor exponent by at
most one. This includes the two endpoint corrections. -/
theorem clampedScaledExponent_difference (t : ℝ) {N : ℕ} (hN : 0 < N)
    (ht : |t| ≤ 1) :
    clampedScaledExponent t N - Int.floor (t*(N : ℝ)) ∈ ({-1,0,1} : Finset ℤ) := by
  have ht' := abs_le.mp ht
  have hNr : (0 : ℤ) < N := by exact_mod_cast hN
  have hlo : -(N : ℤ) ≤ Int.floor (t*(N : ℝ)) := by
    apply Int.le_floor.mpr
    push_cast
    have hh := mul_le_mul_of_nonneg_right ht'.1 (by positivity : 0 ≤ (N : ℝ))
    simpa only [neg_one_mul] using hh
  have hhi : Int.floor (t*(N : ℝ)) ≤ (N : ℤ) := by
    apply Int.floor_le_iff.mpr
    push_cast
    have hh := mul_le_mul_of_nonneg_right ht'.2 (by positivity : 0 ≤ (N : ℝ))
    nlinarith
  simp only [Finset.mem_insert,Finset.mem_singleton]
  unfold clampedScaledExponent
  omega
end DirectedCycles
