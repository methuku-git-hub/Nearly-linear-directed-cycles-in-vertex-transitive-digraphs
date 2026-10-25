module

public import DirectedCycles.ScaledUltraproductPowers
public import DirectedCycles.ShortProgressionProperness

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem scaled_floor_natAbs_lt (t : ℝ) (N : ℕ) (ht : |t| ≤ 1/2) (hN : 3 ≤ N) :
    (Int.floor (t*(N : ℝ))).natAbs < N := by
  apply (int_natAbs_lt_iff _ _).2
  have ht' := abs_le.mp ht
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 := mul_le_mul_of_nonneg_right ht'.1 (by positivity : 0 ≤ (N : ℝ))
  have h2 := mul_le_mul_of_nonneg_right ht'.2 (by positivity : 0 ≤ (N : ℝ))
  have hlo := Int.lt_floor_add_one (t*(N : ℝ))
  have hhi := Int.floor_le (t*(N : ℝ))
  constructor
  · have h : -(N : ℝ) < (Int.floor (t*(N : ℝ)) : ℝ) := by nlinarith
    exact_mod_cast h
  · have h : (Int.floor (t*(N : ℝ)) : ℝ) < (N : ℝ) := by nlinarith
    exact_mod_cast h

open scoped Pointwise
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

theorem scaledUltraPower_mem_internal (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (hN : ∀ᶠ i in (U : Filter ι), 3 ≤ N i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (t : ℝ) (ht : |t| ≤ 1/2) : scaledUltraPower U G u N t ∈ ultraSet (U : Filter ι) G A := by
  apply (ultraMk_mem_ultraSet_iff _ G A _).2
  filter_upwards [hN,hi,hprev] with i hNi hii hpi
  apply shortPowerProgression_subset hii (u i) (N i) hpi
  exact ⟨Int.floor (t*(N i : ℝ)),scaled_floor_natAbs_lt t (N i) ht hNi,rfl⟩
end DirectedCycles
