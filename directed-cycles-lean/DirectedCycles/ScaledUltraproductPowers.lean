module

public import DirectedCycles.UltraproductInternalSets
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- Integer powers with a uniformly finite set of exponents become one fixed
power in an ultraproduct. -/
theorem ultra_zpow_finite_choice (u : ∀ i, G i) (k : ι → ℤ) (S : Finset ℤ)
    (hk : ∀ᶠ i in (U : Filter ι), k i ∈ S) :
    ∃ m ∈ S, ultraMk (U : Filter ι) G (fun i => (u i)^(k i)) =
      (ultraMk (U : Filter ι) G u)^m := by
  have h : ∀ᶠ i in (U : Filter ι), ∃ m : S, k i = m.val := by
    filter_upwards [hk] with i hi
    exact ⟨⟨k i,hi⟩,rfl⟩
  obtain ⟨m,hm⟩ := Ultrafilter.eventually_exists_iff.mp h
  refine ⟨m.val,m.property,?_⟩
  rw [← map_zpow]
  apply (ultraMk_eq_iff _ G _ _).2
  filter_upwards [hm] with i hi
  change (u i)^(k i) = (u i)^m.val
  rw [hi]

/-- Powers at a real proportion of the component scales. -/
noncomputable def scaledUltraPower (u : ∀ i, G i) (N : ι → ℕ) (t : ℝ) : GroupUltraproduct (U : Filter ι) G :=
  ultraMk (U : Filter ι) G (fun i => (u i)^(Int.floor (t*(N i : ℝ))))

theorem scaledUltraPower_zero (u : ∀ i, G i) (N : ι → ℕ) : scaledUltraPower U G u N 0 = 1 := by
  unfold scaledUltraPower
  simp only [zero_mul,Int.floor_zero,zpow_zero]
  exact (ultraMk (U : Filter ι) G).map_one

theorem scaledUltraPower_one (u : ∀ i, G i) (N : ι → ℕ) :
    scaledUltraPower U G u N 1 = ultraMk (U : Filter ι) G (fun i => (u i)^(N i)) := by
  simp [scaledUltraPower]

/-- The addition defect is exactly one of two elements, not an unspecified
infinitesimal. This makes the later descent to a model an explicit proof. -/
theorem scaledUltraPower_add_cases (u : ∀ i, G i) (N : ι → ℕ) (s t : ℝ) :
    scaledUltraPower U G u N (s+t) = scaledUltraPower U G u N s*scaledUltraPower U G u N t ∨
    scaledUltraPower U G u N (s+t) = scaledUltraPower U G u N s*scaledUltraPower U G u N t*
      ultraMk (U : Filter ι) G u := by
  have hc : ∀ᶠ i in (U : Filter ι),
      Int.floor ((s+t)*(N i : ℝ)) = Int.floor (s*(N i : ℝ))+Int.floor (t*(N i : ℝ)) ∨
      Int.floor ((s+t)*(N i : ℝ)) = Int.floor (s*(N i : ℝ))+Int.floor (t*(N i : ℝ))+1 := by
    apply Filter.Eventually.of_forall
    intro i
    have h1 := Int.le_floor_add (s*(N i : ℝ)) (t*(N i : ℝ))
    have h2 := Int.le_floor_add_floor (s*(N i : ℝ)) (t*(N i : ℝ))
    rw [← add_mul] at h1 h2
    omega
  rcases Ultrafilter.eventually_or.mp hc with h | h
  · left
    unfold scaledUltraPower
    rw [← map_mul]
    apply (ultraMk_eq_iff _ G _ _).2
    filter_upwards [h] with i hi
    change (u i)^⌊(s+t)*(N i : ℝ)⌋ = (u i)^⌊s*(N i : ℝ)⌋*(u i)^⌊t*(N i : ℝ)⌋
    rw [hi,zpow_add]
  · right
    unfold scaledUltraPower
    rw [← map_mul,← map_mul]
    apply (ultraMk_eq_iff _ G _ _).2
    filter_upwards [h] with i hi
    change (u i)^⌊(s+t)*(N i : ℝ)⌋ = ((u i)^⌊s*(N i : ℝ)⌋*(u i)^⌊t*(N i : ℝ)⌋)*(u i)
    rw [hi,zpow_add,zpow_add,zpow_one]

/-- Once the infinitesimal generator is killed by a model map, the scaled
powers satisfy the homomorphism law exactly. The map is only required on a
subgroup containing these powers. -/
theorem map_scaledUltraPower_add {H : Type*} [Group H]
    (u : ∀ i, G i) (N : ι → ℕ) (S : Subgroup (GroupUltraproduct (U : Filter ι) G))
    (hu : ultraMk (U : Filter ι) G u ∈ S)
    (hscale : ∀ t : ℝ, scaledUltraPower U G u N t ∈ S)
    (π : S →* H) (hkill : π ⟨ultraMk (U : Filter ι) G u,hu⟩ = 1) (s t : ℝ) :
    π ⟨scaledUltraPower U G u N (s+t),hscale (s+t)⟩ =
      π ⟨scaledUltraPower U G u N s,hscale s⟩*π ⟨scaledUltraPower U G u N t,hscale t⟩ := by
  rcases scaledUltraPower_add_cases U G u N s t with h | h
  · have he : (⟨scaledUltraPower U G u N (s+t),hscale (s+t)⟩ : S) =
        ⟨scaledUltraPower U G u N s,hscale s⟩*⟨scaledUltraPower U G u N t,hscale t⟩ := Subtype.ext h
    rw [he,map_mul]
  · have he : (⟨scaledUltraPower U G u N (s+t),hscale (s+t)⟩ : S) =
        ⟨scaledUltraPower U G u N s,hscale s⟩*⟨scaledUltraPower U G u N t,hscale t⟩*
          ⟨ultraMk (U : Filter ι) G u,hu⟩ := Subtype.ext h
    rw [he,map_mul,map_mul,hkill,mul_one]
end DirectedCycles
