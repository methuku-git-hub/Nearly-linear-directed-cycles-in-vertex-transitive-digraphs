module

public import DirectedCycles.ClampedScaledExponent
public import DirectedCycles.ShortProgressionModelImage

@[expose] public section

set_option autoImplicit false
open scoped Pointwise Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- The model image of the actual short progression is exactly the closed
unit curve segment, including both endpoints. Endpoint powers are clamped
inside the progression and the resulting one-generator error is killed. -/
theorem shortProgression_model_image_eq {H : Type*} [Group H]
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (S : Subgroup (GroupUltraproduct (U : Filter ι) G))
    (hAS : ultraSet (U : Filter ι) G A ⊆ S) (π : S →* H)
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z : S, z.val ∈ ultraSet (U : Filter ι) G A → π z ∈ V)
    (φ : ℝ → H)
    (hφ : ∀ t : ℝ, ∃ h : scaledUltraPower U G u N t ∈ S,
      φ t = π ⟨scaledUltraPower U G u N t,h⟩) :
    π '' (S.subtype ⁻¹' ultraSet (U : Filter ι) G (fun i => shortPowerProgression (u i) (N i))) =
      φ '' Set.Icc (-1 : ℝ) 1 := by
  have hpowers : ∀ n : ℕ, (ultraMk (U : Filter ι) G u)^n ∈ ultraSet (U : Filter ι) G A := by
    intro n
    rw [← map_pow]
    apply (ultraMk_mem_ultraSet_iff _ G A _).2
    filter_upwards [hN n,hprev] with i hNi hpi
    exact hpi n hNi
  have huS : ultraMk (U : Filter ι) G u ∈ S := hAS (by simpa using hpowers 1)
  let uS : S := ⟨ultraMk (U : Filter ι) G u,huS⟩
  have hkill : π uS = 1 := by
    apply hNSS
    intro n
    rw [← map_pow]
    exact himage (uS^n) (hpowers n)
  apply Set.Subset.antisymm
  · rintro y ⟨z,hz,rfl⟩
    obtain ⟨t,ht,he⟩ := shortProgression_model_image U G A u N hN hi hprev S π V hNSS himage φ hφ z hz
    exact ⟨t,ht,he.symm⟩
  · rintro y ⟨t,ht,rfl⟩
    have htabs : |t| ≤ 1 := abs_le.mpr ht
    let k : ι → ℤ := fun i => clampedScaledExponent t (N i)
    let a := ultraMk (U : Filter ι) G (fun i => (u i)^(k i))
    have haP : a ∈ ultraSet (U : Filter ι) G (fun i => shortPowerProgression (u i) (N i)) := by
      apply (ultraMk_mem_ultraSet_iff _ G _ _).2
      filter_upwards [hN 0] with i hNi
      exact ⟨k i,clampedScaledExponent_natAbs_lt t hNi,rfl⟩
    have haA : a ∈ ultraSet (U : Filter ι) G A := by
      apply (ultraMk_mem_ultraSet_iff _ G _ _).2
      filter_upwards [hN 0,hi,hprev] with i hNi hii hpi
      exact shortPowerProgression_subset hii (u i) (N i) hpi
        ⟨k i,clampedScaledExponent_natAbs_lt t hNi,rfl⟩
    have haS := hAS haA
    obtain ⟨htS,hft⟩ := hφ t
    let b : S := ⟨scaledUltraPower U G u N t,htS⟩
    let d : ι → ℤ := fun i => k i-Int.floor (t*(N i : ℝ))
    have hd : ∀ᶠ i in (U : Filter ι), d i ∈ ({-1,0,1} : Finset ℤ) := by
      filter_upwards [hN 0] with i hNi
      exact clampedScaledExponent_difference t hNi htabs
    obtain ⟨m,_,hm⟩ := ultra_zpow_finite_choice U G u d {-1,0,1} hd
    have he : a*(scaledUltraPower U G u N t)⁻¹ = (ultraMk (U : Filter ι) G u)^m := by
      rw [← hm]
      change ultraMk (U : Filter ι) G (fun i => (u i)^(k i))*
        (ultraMk (U : Filter ι) G (fun i => (u i)^(Int.floor (t*(N i : ℝ)))))⁻¹ = _
      rw [← map_inv,← map_mul]
      congr 1
      funext i
      exact (zpow_sub (u i) (k i) (Int.floor (t*(N i : ℝ)))).symm
    have heS : (⟨a,haS⟩ : S)*b⁻¹ = uS^m := Subtype.ext he
    have heπ := congrArg π heS
    simp only [map_mul,map_inv,map_zpow,hkill,one_zpow,mul_inv_eq_one] at heπ
    refine ⟨⟨a,haS⟩,haP,?_⟩
    exact heπ.trans hft.symm

/-- In a continuous model the central progression has compact image, by the
exact interval identification rather than merely a one-sided containment. -/
theorem shortProgression_image_compact {H : Type*} [TopologicalSpace H]
    {T : Set H} {φ : ℝ → H} (hφ : Continuous φ)
    (he : T = φ '' Set.Icc (-1 : ℝ) 1) : IsCompact T := by
  rw [he]
  exact isCompact_Icc.image hφ
end DirectedCycles
