module

public import DirectedCycles.LocalScaledPowers
public import DirectedCycles.LocalPowerSegmentMaps
public import DirectedCycles.LocalCurveExtension
public import DirectedCycles.LocalInternalSetLogic
public import DirectedCycles.ScaledPowerInterval

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i))

/-- An actual local model kills an infinitesimal generator because every
standard power has its image in a cyclic NSS region. -/
theorem local_model_kills_generator {H : Type*} [Group H]
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), N i ≤ M i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ x ∈ localUltraSet (U : Filter ι) G A, π.toFun x ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G u) = 1 := by
  apply hNSS
  intro n
  have hn : ∀ᶠ i in (U : Filter ι), n ≤ M i := by
    filter_upwards [hN n,hM] with i hni hmi
    omega
  rw [← map_localUltraSegment (U : Filter ι) G L u M p π n hn]
  apply himage
  apply (localUltraMk_mem_iff (U : Filter ι) G A _).2
  filter_upwards [hN n,hprev] with i hni hpi
  exact hpi n hni

/-- Scaled values in the middle half of a local power segment remain in the
internal approximate group; negative indices use the actual inverse map. -/
theorem localScaledPower_mem_internal (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ᶠ i in (U : Filter ι), 3 ≤ N i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (t : ℝ) (ht : |t| ≤ 1/2) :
    localScaledPower U G L u N M p t ∈ localUltraSet (U : Filter ι) G A := by
  apply (localUltraMk_mem_iff (U : Filter ι) G A _).2
  filter_upwards [hN,hi,hprev] with i hNi hii hpi
  have hn := scaled_floor_natAbs_lt t (N i) ht hNi
  dsimp only [LocalGroupAlgebra.PowerSegment.signedPower]
  split_ifs
  · exact hpi _ hn
  · exact hii _ (hpi _ hn)

/-- A compact NSS target region and an inner model neighbourhood produce a
nontrivial continuous one-parameter map from actual local component segments.
The source is not assumed to embed in a global group. -/
theorem exists_local_scaled_one_parameter {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H]
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (p i).power (N i) ∉ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V)
    (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ x ∈ localUltraSet (U : Filter ι) G A, π.toFun x ∈ V)
    (W : Set H) (hW1 : (1 : H) ∈ W)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ localUltraSet (U : Filter ι) G A) :
    ∃ φ : ℝ → H, Continuous φ ∧ φ 0 = 1 ∧
      (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
      (∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t)) := by
  have hN2 : ∀ᶠ i in (U : Filter ι), 1 ≤ N i ∧ 2*N i ≤ M i := by
    filter_upwards [hN 0,hM] with i hni hmi
    exact ⟨by omega,hmi⟩
  have hkill := local_model_kills_generator U G L A u N M p hN
    (hM.mono fun _ h => by omega) hprev π V hNSS himage
  let f : ℝ → H := fun t => π.toFun (localScaledPower U G L u N M p t)
  have h0 : f 0 = 1 := by
    dsimp only [f]
    rw [localScaledPower_zero]
    exact π.map_one
  have hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → f (s+t) = f s*f t := by
    intro s t hst
    have hs : |s| ≤ 1 := by linarith [abs_nonneg t]
    have ht : |t| ≤ 1 := by linarith [abs_nonneg s]
    have hsum : |s+t| ≤ 1 := (abs_add_le _ _).trans hst
    rcases localScaledPower_add_cases U G L u N M p hd hr hN2 s t hs ht hsum with h | ⟨z,hz,hz'⟩
    · exact (π.map_mul h).symm
    · have he := π.map_mul hz'
      change π.toFun z*π.toFun (localUltraMk (U : Filter ι) G u) = f (s+t) at he
      rw [hkill,mul_one] at he
      exact he.symm.trans (π.map_mul hz).symm
  obtain ⟨φ,hφ0,hφadd,hagree⟩ := exists_local_curve_extension f h0 (by norm_num : (0 : ℝ)<1) hadd
  have hbound : ∀ t : ℝ, |t| ≤ 1/2 → φ t ∈ V := by
    intro t ht
    rw [hagree t (by linarith)]
    exact himage _ (localScaledPower_mem_internal U G L A u N M p
      ((hN 2).mono fun _ h => by omega) hi hprev t ht)
  have hcont := continuous_curve_of_compact_nss φ hφ0 hφadd hV hNSS (by norm_num : (0 : ℝ)<1/2) hbound
  refine ⟨φ,hcont,hφ0,hφadd,?_,hagree⟩
  intro he
  have hm : localScaledPower U G L u N M p 1 ∈ localUltraSet (U : Filter ι) G A := by
    apply hsmall
    have hf : f 1 = 1 := (hagree 1 (by norm_num)).symm.trans he
    simpa only [show π.toFun (localScaledPower U G L u N M p 1) = 1 from hf] using hW1
  rw [localScaledPower_one] at hm
  have hh := (localUltraMk_mem_iff (U : Filter ι) G A _).1 hm
  obtain ⟨i,hai,hbi⟩ := (hh.and hexit).exists
  exact hbi hai
end DirectedCycles
