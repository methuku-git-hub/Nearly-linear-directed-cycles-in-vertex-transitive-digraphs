import DirectedCycles.LocalToLocalInfinitesimalGenerator
import DirectedCycles.LocalCurvePowerTrappingContinuity
import DirectedCycles.LocalScaledModel

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i))

/-- Actual local component power segments construct a nontrivial continuous
local curve in a local target. Infinitesimal rounding is killed by the proved
power-sequence condition; finite-power trapping supplies continuity. -/
theorem exists_local_to_local_scaled_curve {H : Type*} [TopologicalSpace H]
    (Q : LocalGroupAlgebra H) (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (p i).power (N i) ∉ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H)
    (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (htrap : ∀ O : Set H, O ∈ 𝓝 Q.one → ∃ k : ℕ, 1 ≤ k ∧
      ∀ x : H, (∀ n ≤ k, Q.PowerIn V x n) → x ∈ O)
    (himage : ∀ x ∈ localUltraSet (U : Filter ι) G A, π.toFun x ∈ V)
    (W : Set H) (hW1 : Q.one ∈ W)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ localUltraSet (U : Filter ι) G A) :
    ∃ f : ℝ → H, ContinuousAt f 0 ∧ f 0 = Q.one ∧
      (∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t))) ∧ f 1 ≠ Q.one ∧
      (∀ t : ℝ, f t = π.toFun (localScaledPower U G L u N M p t)) := by
  have hN2 : ∀ᶠ i in (U : Filter ι), 1 ≤ N i ∧ 2*N i ≤ M i := by
    filter_upwards [hN 0,hM] with i hni hmi
    exact ⟨by omega,hmi⟩
  have hkill := local_to_local_model_kills_generator U G L Q A u N M p hN
    (hM.mono fun _ h => by omega) hprev π V hNSS himage
  let f : ℝ → H := fun t => π.toFun (localScaledPower U G L u N M p t)
  have h0 : f 0 = Q.one := by
    dsimp only [f]
    rw [localScaledPower_zero]
    exact π.map_one
  have hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)) := by
    intro s t hst
    have hs : |s| ≤ 1 := by linarith [abs_nonneg t]
    have ht : |t| ≤ 1 := by linarith [abs_nonneg s]
    have hsum : |s+t| ≤ 1 := (abs_add_le _ _).trans hst
    rcases localScaledPower_add_cases U G L u N M p hd hr hN2 s t hs ht hsum with h | ⟨z,hz,hz'⟩
    · exact π.map_mul h
    · have he := π.map_mul hz'
      rw [hkill] at he
      have heq : f (s+t) = π.toFun z := Q.unique he (Q.mul_one _)
      rw [heq]
      exact π.map_mul hz
  have hbound : ∀ t : ℝ, |t| ≤ 1/2 → f t ∈ V := by
    intro t ht
    exact himage _ (localScaledPower_mem_internal U G L A u N M p
      ((hN 2).mono fun _ h => by omega) hi hprev t ht)
  refine ⟨f,local_curve_continuousAt_of_power_trapping Q f h0 (by norm_num : (0 : ℝ)<1)
    hadd V (by norm_num : (0 : ℝ)<1/2) hbound htrap,h0,hadd,?_,fun _ => rfl⟩
  intro he
  have hm : localScaledPower U G L u N M p 1 ∈ localUltraSet (U : Filter ι) G A := by
    apply hsmall
    simpa only [show π.toFun (localScaledPower U G L u N M p 1) = Q.one from he] using hW1
  rw [localScaledPower_one] at hm
  have hh := (localUltraMk_mem_iff (U : Filter ι) G A _).1 hm
  obtain ⟨i,hai,hbi⟩ := (hh.and hexit).exists
  exact hbi hai
end DirectedCycles
