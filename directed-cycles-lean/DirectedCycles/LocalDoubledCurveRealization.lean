module

public import DirectedCycles.LocalBoundedScaledExponentLimit
public import DirectedCycles.LocalScaledModel

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- The specified scaled curve formula extends to the doubled interval
using genuine products in a fourfold certified segment. -/
theorem local_scaled_curve_formula_double {H : Type*} [Group H]
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 4*N i ≤ M i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (φ : ℝ → H) (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hformula : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t)) :
    ∀ t : ℝ, |t| ≤ 2 → φ t = π.toFun (localScaledPower U G L u N M p t) := by
  have hkill := local_model_kills_generator U G L A u N M p hN (hM.mono fun _ h => by omega)
    hprev π V hNSS himage
  have hdom : ∀ᶠ i in (U : Filter ι), 1 ≤ N i ∧ 2*(2*N i) ≤ M i := by
    filter_upwards [hN 0,hM] with i hni hmi
    exact ⟨by omega,by omega⟩
  intro t ht
  have hhalf : |t/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have hhalf2 : |t/2| ≤ (2 : ℕ) := hhalf.trans (by norm_num)
  have hsum : |t/2+t/2| ≤ (2 : ℕ) := by simpa only [add_halves,Nat.cast_ofNat] using ht
  have he : π.toFun (localScaledPower U G L u N M p (t/2+t/2)) =
      π.toFun (localScaledPower U G L u N M p (t/2))*π.toFun (localScaledPower U G L u N M p (t/2)) := by
    rcases localScaledPower_add_cases_bounded U G L u N M p 2 (by omega) hd hr hdom
      (t/2) (t/2) hhalf2 hhalf2 hsum with h | ⟨z,hz,hz'⟩
    · exact (π.map_mul h).symm
    · have hh := π.map_mul hz'
      change π.toFun z*π.toFun (localUltraMk (U : Filter ι) G u) = _ at hh
      rw [hkill,mul_one] at hh
      exact hh.symm.trans (π.map_mul hz).symm
  rw [← hformula (t/2) hhalf,← hadd,add_halves] at he
  exact he.symm

/-- A variable signed exponent up to twice the first-exit scale has the
model image prescribed by its real scale limit, including either sign. -/
theorem local_model_doubled_exponent_limit {H : Type*} [Group H]
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i)) (k : ι → ℤ) (t : ℝ)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 4*N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hk : ∀ᶠ i in (U : Filter ι), (k i).natAbs ≤ 2*N i) (ht : |t| ≤ 2)
    (hlim : Filter.Tendsto (fun i => (k i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (φ : ℝ → H) (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hformula : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t)) :
    π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i))) = φ t := by
  have he := local_model_scaled_exponent_limit_bounded U G L 2 (by omega) hd hr A u N M p k t
    hN (hM.mono fun _ h => by omega) hi hprev hk ht hlim π V hNSS himage
  exact he.trans (local_scaled_curve_formula_double U G L hd hr A u N M p hN hM hprev
    π V hNSS himage φ hadd hformula t ht).symm
end DirectedCycles
