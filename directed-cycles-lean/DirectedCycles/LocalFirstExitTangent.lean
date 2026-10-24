import DirectedCycles.LocalShortProgressionModel
import DirectedCycles.LieCurveCoordinateComparison

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- The actual scaled first-exit curve has tangent in the annulus prescribed
by the model sandwich. Endpoint inclusion in the outer closed ball follows
from the exact image of the short progression, not from a fictitious last
power belonging to the source set. -/
theorem local_first_exit_tangent_annulus
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (p i).power (N i) ∉ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (φ : ℝ → H) (hφ0 : φ 0 = 1) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hformula : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t))
    {v : E} (hv : HasDerivAt (fun t => chartAt E (1 : H) (φ t)-chartAt E (1 : H) 1) v 0)
    {R ρ σ : ℝ} (hσ : 0 ≤ σ) (hσR : σ < R)
    (hinj : Set.InjOn (lieExponential (G := H) (E := E)) (Metric.ball 0 R))
    (houter : ∀ z ∈ localUltraSet (U : Filter ι) G A,
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) σ)
    (hinner : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ρ →
      z ∈ localUltraSet (U : Filter ι) G A) : ρ ≤ ‖v‖ ∧ ‖v‖ ≤ σ := by
  have heq := local_shortProgression_model_image_eq U G L hd hr A u N M p hN hM hi hprev
    π V hNSS himage φ hformula
  apply lie_curve_tangent_annulus hσ hσR hinj φ hφ0 hφc hφadd hv
  · intro t ht
    have hm : φ t ∈ π.toFun '' localUltraSet (U : Filter ι) G (fun i => (p i).shortSignedSet (N i)) := by
      rw [heq]
      exact ⟨t,abs_le.mp ht,rfl⟩
    obtain ⟨z,hz,he⟩ := hm
    rw [← he]
    apply houter z
    obtain ⟨x,rfl⟩ := Quotient.exists_rep z
    apply (localUltraMk_mem_iff (U : Filter ι) G A x).2
    have hx := (localUltraMk_mem_iff (U : Filter ι) G _ x).1 hz
    filter_upwards [hx,hi,hprev] with i hxi hii hpi
    obtain ⟨k,hk,hke⟩ := hxi
    rw [← hke]
    dsimp only [LocalGroupAlgebra.PowerSegment.signedPower]
    split_ifs
    · exact hpi _ hk
    · exact hii _ (hpi _ hk)
  · intro hh
    rw [hformula 1 (by norm_num),localScaledPower_one] at hh
    have hm := (localUltraMk_mem_iff (U : Filter ι) G A _).1 (hinner _ hh)
    obtain ⟨i,hmi,hei⟩ := (hm.and hexit).exists
    exact hei hmi
end DirectedCycles
