import DirectedCycles.LocalToLocalDoubledCurveRealization
import DirectedCycles.LocalToLocalClosedScaledExponentLimit
import DirectedCycles.LocalNestedSegmentComparison
import DirectedCycles.BoundedSignedRatioLimit
import DirectedCycles.LocalUniformSegmentMembership
import DirectedCycles.LocalExponentialRadialLaw
import DirectedCycles.LocalRoundedCorrections
import DirectedCycles.LocalMinimalLiftImprovement
import DirectedCycles.LocalLieTargetCorrectedModelControl

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    {Q : LocalGroupAlgebra H} (Y : LocalExponentialData (E := E) Q)

/-- The finite least-lift property contradicts a collinear first-exit model
with the quantitative nested-scale bounds. Signed corrections, their actual
local power domains, uniform source membership and strict escape improvement
are constructed in this deduction. Obtaining the collinear model and the
unbounded least-lift exit times remains the preceding lifting argument. -/
theorem local_lie_target_central_correction_contradiction
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (B : ∀ i, Finset (G i)) (g u : ∀ i, G i) (N₁ M₁ N₀ M₀ : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (g i) (M₁ i))
    (q : ∀ i, (L i).PowerSegment (u i) (M₀ i))
    (hN₁ : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N₁ i)
    (hN₀ : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N₀ i)
    (hM₁ : ∀ i, 2*N₁ i ≤ M₁ i)
    (hM₀ : ∀ i, 4*N₀ i ≤ M₀ i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ B i, (L i).inv x ∈ B i)
    (hp : ∀ᶠ i in (U : Filter ι), ∀ n < N₁ i, (p i).power n ∈ B i)
    (hq : ∀ᶠ i in (U : Filter ι), ∀ n < N₀ i, (q i).power n ∈ B i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H) (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))), π.toFun z ∈ V)
    (φ ψ : ℝ → H)
    (hφ : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L g N₁ M₁ p t))
    (hψ : ∀ t : ℝ, |t| ≤ 1 → ψ t = π.toFun (localScaledPower U G L u N₀ M₀ q t))
    (hψadd : ∀ s t : ℝ, |s|+|t| ≤ 2 → Q.mulRel (ψ s) (ψ t) (ψ (s+t)))
    {r δ t t' : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (X : E) (hX : ‖X‖ ≤ (1001/1000)*r)
    (hφexp : ∀ s : ℝ, |s| ≤ 1 → φ s = Y.chart ((t*s) • X))
    (hψexp : ∀ s : ℝ, |s| ≤ 2 → ψ s = Y.chart ((t'*s) • X))
    (hwide : (|t|+2*|t'|)*‖X‖ < Y.radius)
    (ht : |t| ≤ (11/10)*δ) (ht'lo : (9/10)*δ ≤ t') (ht'hi : t' ≤ (11/10)*δ)
    (hratio : ∀ᶠ i in (U : Filter ι), (N₁ i : ℝ) ≤ (11/10)*(N₀ i : ℝ))
    (hinner : ∀ z, π.toFun z ∈ Y.chart '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (hN₀pos : ∀ i, 0 < N₀ i) (hN₁pos : ∀ i, 0 < N₁ i)
    (C P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))
    (hB : ∀ i, (B i : Set (G i)) ⊆ (D i).small) (hg : ∀ i, g i ∈ B i)
    (hmin : ∀ i, ∀ z : (D i).small, z.val ∈ B i →
      (D i).project z = (D i).project ⟨g i,hB i (hg i)⟩ →
        (L i).escapeNorm (B i : Set (G i)) (g i) ≤ (L i).escapeNorm (B i : Set (G i)) z.val)
    (hnorm : ∀ i, (L i).escapeNorm (B i : Set (G i)) (g i) = 1/(N₁ i : ℝ))
    (hCi : ∀ i, ∀ x ∈ C i, (L i).inv x ∈ C i)
    (hCdom : ∀ i, (L i).AllProductsDefined (C i) 4)
    (huC : ∀ i, u i ∈ C i)
    (hpC : ∀ i, ∀ n ≤ N₁ i, (p i).power n ∈ C i)
    (hqC : ∀ i, ∀ n ≤ 2*N₀ i, (q i).power n ∈ C i)
    (hgu : ∀ i, (L i).Commute (g i) (u i))
    (hP : ∀ i, ∀ k : ℤ, k.natAbs < N₀ i → (q i).signedPower k ∈ P i) : False := by
  classical
  obtain ⟨m,hm,herr⟩ := exists_rounded_correction_family N₀ N₁ hN₀pos hN₁pos hδ ht ht'lo ht'hi
  let p' : ∀ i, (L i).PowerSegment (g i) (N₁ i) := fun i =>
    ⟨(p i).power,fun n hn => (p i).product n (hn.trans (by have := hM₁ i; omega))⟩
  let q' : ∀ i, (L i).PowerSegment (u i) (2*N₀ i) := fun i =>
    ⟨(q i).power,fun n hn => (q i).product n (hn.trans (by have := hM₀ i; omega))⟩
  choose h hprod s hs using fun i => exists_corrected_segment_left (L i) (hd i) (hr i)
    (hCi i) (hCdom i) (huC i) (hN₁pos i) (p' i) (q' i) (hpC i) (hqC i) (hgu i) (m i) (hm i)
  have hstay := local_lie_target_corrected_model_control U G L Y hd hr (fun i => (B i : Set (G i)))
    g u N₁ M₁ N₀ M₀ p q hN₁ hN₀ (Filter.Eventually.of_forall hM₁)
    (Filter.Eventually.of_forall hM₀) hi hp hq π V hNSS himage φ ψ hφ hψ hψadd hr0 hδ X hX
    hφexp hψexp hwide hinner m (fun i => (s i).power) (Filter.Eventually.of_forall hm)
    (Filter.Eventually.of_forall hs) (hratio.mono fun i hi => herr i hi)
  obtain ⟨i,hstayi,hlarge⟩ := (hstay.and (hN₁ 2)).exists
  have hmi : (-(m i)).natAbs < N₀ i := by
    rw [Int.natAbs_neg]
    have hb := hm i
    have hp0 := hN₀pos i
    by_contra hh
    have hh' : N₀ i ≤ (m i).natAbs := le_of_not_gt hh
    nlinarith
  exact (D i).minimal_lift_excludes_corrected_segment (hd i) (B i) (hB i)
    ⟨g i,hB i (hg i)⟩ (hg i) (hmin i) (hP i _ hmi) (hprod i) (hN₁pos i) (s i) hstayi (hnorm i)
end DirectedCycles
