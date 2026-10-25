module

public import DirectedCycles.InfinitesimalScaledPowers

@[expose] public section

set_option autoImplicit false
open scoped Pointwise Topology
namespace DirectedCycles

/-- Dividing the floor error by the exit time gives an error below 1/N. -/
theorem scaled_floor_error (t : ℝ) {N : ℕ} (hN : 0 < N) :
    |t-(Int.floor (t*(N : ℝ)) : ℝ)/(N : ℝ)| < 1/(N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := Int.floor_le (t*(N : ℝ))
  have hhi := Int.lt_floor_add_one (t*(N : ℝ))
  have he : t-(Int.floor (t*(N : ℝ)) : ℝ)/(N : ℝ) =
      (t*(N : ℝ)-(Int.floor (t*(N : ℝ)) : ℝ))/(N : ℝ) := by field_simp
  rw [he,abs_div,abs_of_pos hNr,abs_of_nonneg (sub_nonneg.mpr hlo)]
  exact div_lt_div_of_pos_right (by linarith) hNr

/-- Convergence of the normalized exponent makes its difference from the
canonical scaled exponent infinitesimal. -/
theorem scaled_exponent_difference_small {ι : Type*} (U : Ultrafilter ι)
    (N : ι → ℕ) (k : ι → ℤ) (t : ℝ)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (ht : Filter.Tendsto (fun i => (k i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      |((k i-Int.floor (t*(N i : ℝ)) : ℤ) : ℝ)/(N i : ℝ)| < ε := by
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (half_pos hε)
  have hclose : ∀ᶠ i in (U : Filter ι), |(k i : ℝ)/(N i : ℝ)-t| < ε/2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ht (ε/2) (half_pos hε))
  filter_upwards [hN (m+1),hclose] with i hNi hti
  have hNpos : 0 < N i := by omega
  have hNr : (m : ℝ)+1 ≤ N i := by exact_mod_cast (show m+1 ≤ N i by omega)
  have hinv : 1/(N i : ℝ) < ε/2 :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hNr) hm
  have herr := scaled_floor_error t hNpos
  calc
    |((k i-Int.floor (t*(N i : ℝ)) : ℤ) : ℝ)/(N i : ℝ)| =
        |((k i : ℝ)/(N i : ℝ)-t)+(t-(Int.floor (t*(N i : ℝ)) : ℝ)/(N i : ℝ))| := by
          congr 1
          push_cast
          ring
    _ ≤ |(k i : ℝ)/(N i : ℝ)-t|+|t-(Int.floor (t*(N i : ℝ)) : ℝ)/(N i : ℝ)| := abs_add_le _ _
    _ < ε := by linarith

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- Model images of variable powers depend only on the limit of the exponent
divided by the first exit time. The kernel equality is derived from NSS. -/
theorem model_scaled_exponent_limit {H : Type*} [Group H]
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ) (k : ι → ℤ) (t : ℝ)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (ht : Filter.Tendsto (fun i => (k i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t))
    (S : Subgroup (GroupUltraproduct (U : Filter ι) G)) (π : S →* H)
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z : S, z.val ∈ ultraSet (U : Filter ι) G A → π z ∈ V)
    (hk : ultraMk (U : Filter ι) G (fun i => (u i)^(k i)) ∈ S)
    (htS : scaledUltraPower U G u N t ∈ S) :
    π ⟨ultraMk (U : Filter ι) G (fun i => (u i)^(k i)),hk⟩ =
      π ⟨scaledUltraPower U G u N t,htS⟩ := by
  let a : S := ⟨ultraMk (U : Filter ι) G (fun i => (u i)^(k i)),hk⟩
  let b : S := ⟨scaledUltraPower U G u N t,htS⟩
  let d : ι → ℤ := fun i => k i-Int.floor (t*(N i : ℝ))
  have he : ultraMk (U : Filter ι) G (fun i => (u i)^(d i)) = (a*b⁻¹).val := by
    change _ = ultraMk (U : Filter ι) G (fun i => (u i)^(k i))*
      (ultraMk (U : Filter ι) G (fun i => (u i)^(Int.floor (t*(N i : ℝ)))))⁻¹
    rw [← map_inv,← map_mul]
    congr 1
    funext i
    exact zpow_sub (u i) (k i) (Int.floor (t*(N i : ℝ)))
  have hdS : ultraMk (U : Filter ι) G (fun i => (u i)^(d i)) ∈ S := he.symm ▸ (a*b⁻¹).property
  have hkill := map_infinitesimal_scaled_power U G A u N d (hN 0) hi hprev
    (scaled_exponent_difference_small U N k t hN ht) S π V hNSS himage hdS
  have heS : (⟨ultraMk (U : Filter ι) G (fun i => (u i)^(d i)),hdS⟩ : S) = a*b⁻¹ := Subtype.ext he
  rw [heS,map_mul,map_inv,mul_inv_eq_one] at hkill
  exact hkill
end DirectedCycles
