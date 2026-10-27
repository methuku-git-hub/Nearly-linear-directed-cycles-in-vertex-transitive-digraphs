module

public import DirectedCycles.ShortProgressionModelImage

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- A uniformly bounded signed integer ratio has a real ultralimit in the
same closed interval, including either endpoint. -/
theorem bounded_signed_ratio_ultralimit {ι : Type*} (U : Ultrafilter ι)
    (N : ι → ℕ) (k : ι → ℤ) (C : ℕ)
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hk : ∀ᶠ i in (U : Filter ι), (k i).natAbs ≤ C*N i) :
    ∃ t : ℝ, |t| ≤ (C : ℝ) ∧
      Filter.Tendsto (fun i => (k i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t) := by
  let r : ι → ℝ := fun i => (k i : ℝ)/(N i : ℝ)
  have hr : Set.Icc (-(C : ℝ)) C ∈ Ultrafilter.map r U := by
    change ∀ᶠ i in (U : Filter ι), r i ∈ Set.Icc (-(C : ℝ)) C
    filter_upwards [hN,hk] with i hni hki
    have hpos : (0 : ℝ) < N i := by exact_mod_cast hni
    have hbound : |(k i : ℝ)| ≤ (C : ℝ)*(N i : ℝ) := by
      have hh : ((k i).natAbs : ℝ) ≤ (C : ℝ)*(N i : ℝ) := by exact_mod_cast hki
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
    apply abs_le.mp
    dsimp only [r]
    rw [abs_div,abs_of_pos hpos]
    exact (div_le_iff₀ hpos).2 hbound
  obtain ⟨t,ht,hlim⟩ := isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map r U) hr
  refine ⟨t,abs_le.mpr ht,?_⟩
  change Filter.map r (U : Filter ι) ≤ 𝓝 t
  simpa only [Ultrafilter.coe_map] using hlim
end DirectedCycles
