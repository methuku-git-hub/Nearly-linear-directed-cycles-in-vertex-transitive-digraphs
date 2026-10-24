import DirectedCycles.LocalClosedScaledExponentLimit
import DirectedCycles.ShortProgressionModelImage

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- Bounded positive integer scale ratios have a real ultralimit in [0,1]. -/
theorem bounded_nat_ratio_ultralimit {ι : Type*} (U : Ultrafilter ι) (N K : ι → ℕ)
    (hle : ∀ᶠ i in (U : Filter ι), K i ≤ N i) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun i => (K i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t) := by
  let r : ι → ℝ := fun i => (K i : ℝ)/(N i : ℝ)
  have hr : Set.Icc (0 : ℝ) 1 ∈ Ultrafilter.map r U := by
    change ∀ᶠ i in (U : Filter ι), r i ∈ Set.Icc (0 : ℝ) 1
    filter_upwards [hle] with i hi
    refine ⟨by dsimp only [r]; positivity,?_⟩
    dsimp only [r]
    exact div_le_one_of_le₀ (by exact_mod_cast hi) (by positivity)
  obtain ⟨t,ht,hlim⟩ := isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map r U) hr
  refine ⟨t,ht,?_⟩
  change Filter.map r (U : Filter ι) ≤ 𝓝 t
  simpa only [Ultrafilter.coe_map] using hlim

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Comparing two genuine segments of the same generator identifies the
small-scale endpoint with a point on the large-scale curve. The scale ratio
is obtained by compactness; equality uses actual power uniqueness and NSS. -/
theorem local_nested_segment_comparison {H : Type*} [Group H]
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M K J : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (q : ∀ i, (L i).PowerSegment (u i) (J i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hK : ∀ᶠ i in (U : Filter ι), K i ≤ N i ∧ K i ≤ J i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (φ ψ : ℝ → H)
    (hφ : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t))
    (hψ : ψ 1 = π.toFun (localScaledPower U G L u K J q 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun i => (K i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t) ∧ ψ 1 = φ t := by
  obtain ⟨t,ht,hlim⟩ := bounded_nat_ratio_ultralimit U N K (hK.mono fun _ h => h.1)
  have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have he := local_model_scaled_exponent_limit_closed U G L hd hr A u N M p
    (fun i => (K i : ℤ)) t hN hM hi hprev
    (hK.mono fun i h => by simpa only [Int.natAbs_natCast] using h.1) habs
    (by simpa only [Int.cast_natCast] using hlim) π V hNSS himage
  have heq : localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (K i : ℤ)) =
      localScaledPower U G L u K J q 1 := by
    rw [localScaledPower_one]
    apply Quotient.sound
    filter_upwards [hM,hK] with i hmi hki
    rw [(p i).signedPower_nat]
    exact ((p i).product (K i) (by omega)).unique (L i) ((q i).product (K i) hki.2)
  refine ⟨t,ht,hlim,?_⟩
  rw [heq,← hφ t habs,← hψ] at he
  exact he
end DirectedCycles
