module

public import DirectedCycles.ClampedScaledExponent
public import DirectedCycles.ScaledExponentLimit

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- The interior clamped exponents converge to every point of the closed
unit interval, including the endpoints. -/
theorem clamped_exponent_tendsto {ι : Type*} (U : Ultrafilter ι) (N : ι → ℕ)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i) (t : ℝ) (ht : |t| ≤ 1) :
    Filter.Tendsto (fun i => (clampedScaledExponent t (N i) : ℝ)/(N i : ℝ))
      (U : Filter ι) (𝓝 t) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (half_pos hε)
  filter_upwards [hN (m+1)] with i hNi
  have hNpos : 0 < N i := by omega
  have hNr : (0 : ℝ) < N i := by exact_mod_cast hNpos
  have hNm : (m : ℝ)+1 ≤ N i := by exact_mod_cast (show m+1 ≤ N i by omega)
  have hinv : 1/(N i : ℝ) < ε/2 :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hNm) hm
  have hd := clampedScaledExponent_difference t hNpos ht
  have hdiff : |(clampedScaledExponent t (N i) : ℝ)-(Int.floor (t*(N i : ℝ)) : ℝ)| ≤ 1 := by
    have hd' : |clampedScaledExponent t (N i)-Int.floor (t*(N i : ℝ))| ≤ (1 : ℤ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd
      rcases hd with hd | hd | hd <;> rw [hd] <;> norm_num
    exact_mod_cast hd'
  have hratio : |(clampedScaledExponent t (N i) : ℝ)/(N i : ℝ)-
      (Int.floor (t*(N i : ℝ)) : ℝ)/(N i : ℝ)| ≤ 1/(N i : ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hNr]
    exact div_le_div_of_nonneg_right hdiff hNr.le
  have herr := scaled_floor_error t hNpos
  rw [Real.dist_eq]
  calc
    |(clampedScaledExponent t (N i) : ℝ)/(N i : ℝ)-t| =
        |((clampedScaledExponent t (N i) : ℝ)/(N i : ℝ)-(Int.floor (t*(N i : ℝ)) : ℝ)/(N i : ℝ))+
          ((Int.floor (t*(N i : ℝ)) : ℝ)/(N i : ℝ)-t)| := by congr 1; ring
    _ ≤ |(clampedScaledExponent t (N i) : ℝ)/(N i : ℝ)-(Int.floor (t*(N i : ℝ)) : ℝ)/(N i : ℝ)|+
          |(Int.floor (t*(N i : ℝ)) : ℝ)/(N i : ℝ)-t| := abs_add_le _ _
    _ < ε := by rw [abs_sub_comm] at herr; linarith
end DirectedCycles
