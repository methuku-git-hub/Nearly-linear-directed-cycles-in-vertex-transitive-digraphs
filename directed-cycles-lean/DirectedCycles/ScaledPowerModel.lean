import DirectedCycles.ScaledPowerClosure
import DirectedCycles.ScaledPowerInterval
import DirectedCycles.CompactNSSCurve

set_option autoImplicit false
open scoped Pointwise Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- Unbounded first-exit times, a compact cyclic-NSS image region, and an inner
model neighbourhood produce an actual nontrivial continuous one-parameter
map. Its construction uses the given map only on its generated subgroup. -/
theorem exists_scaled_one_parameter {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H]
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (u i)^(N i) ∉ A i)
    (π : Subgroup.closure (ultraSet (U : Filter ι) G A) →* H)
    (V : Set H) (hV : IsCompact V)
    (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ x : Subgroup.closure (ultraSet (U : Filter ι) G A),
      x.val ∈ ultraSet (U : Filter ι) G A → π x ∈ V)
    (W : Set H) (hW1 : (1 : H) ∈ W)
    (hsmall : ∀ x : Subgroup.closure (ultraSet (U : Filter ι) G A),
      π x ∈ W → x.val ∈ ultraSet (U : Filter ι) G A) :
    ∃ φ : ℝ → H, Continuous φ ∧ φ 0 = 1 ∧
      (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
      (∀ t : ℝ, ∃ h : scaledUltraPower U G u N t ∈ Subgroup.closure (ultraSet (U : Filter ι) G A),
        φ t = π ⟨scaledUltraPower U G u N t,h⟩) := by
  let B := ultraSet (U : Filter ι) G A
  let S := Subgroup.closure B
  have hN2 : ∀ᶠ i in (U : Filter ι), 2 ≤ N i := (hN 1).mono fun _ h => by omega
  have hN3 : ∀ᶠ i in (U : Filter ι), 3 ≤ N i := (hN 2).mono fun _ h => by omega
  have hpowers : ∀ n : ℕ, (ultraMk (U : Filter ι) G u)^n ∈ B := by
    intro n
    rw [← map_pow]
    apply (ultraMk_mem_ultraSet_iff _ G A _).2
    filter_upwards [hN n,hprev] with i hNi hpi
    exact hpi n hNi
  have huB : ultraMk (U : Filter ι) G u ∈ B := by simpa using hpowers 1
  have huS : ultraMk (U : Filter ι) G u ∈ S := Subgroup.subset_closure huB
  have hscale : ∀ t : ℝ, scaledUltraPower U G u N t ∈ S :=
    scaledUltraPower_mem_closure U G A u N hN2 hprev
  let uS : S := ⟨ultraMk (U : Filter ι) G u,huS⟩
  have hkill : π uS = 1 := by
    apply hNSS
    intro n
    rw [← map_pow]
    exact himage (uS^n) (hpowers n)
  let φ : ℝ → H := fun t => π ⟨scaledUltraPower U G u N t,hscale t⟩
  have h0 : φ 0 = 1 := by
    have he : (⟨scaledUltraPower U G u N 0,hscale 0⟩ : S) = 1 :=
      Subtype.ext (scaledUltraPower_zero U G u N)
    change π ⟨scaledUltraPower U G u N 0,hscale 0⟩ = 1
    rw [he,map_one]
  have hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t := by
    intro s t
    exact map_scaledUltraPower_add U G u N S huS hscale π hkill s t
  have hbound : ∀ t : ℝ, |t| ≤ 1/2 → φ t ∈ V := by
    intro t ht
    apply himage
    exact scaledUltraPower_mem_internal U G A u N hN3 hi hprev t ht
  have hcont : Continuous φ := continuous_curve_of_compact_nss φ h0 hadd hV hNSS (by norm_num) hbound
  refine ⟨φ,hcont,h0,hadd,?_,fun t => ⟨hscale t,rfl⟩⟩
  intro he
  have hmem : scaledUltraPower U G u N 1 ∈ B :=
    hsmall ⟨scaledUltraPower U G u N 1,hscale 1⟩ (by change φ 1 ∈ W; simpa only [he] using hW1)
  rw [scaledUltraPower_one] at hmem
  have hh := (ultraMk_mem_ultraSet_iff _ G A _).1 hmem
  obtain ⟨i,hi',hi''⟩ := (hh.and hexit).exists
  exact hi'' hi'
end DirectedCycles
