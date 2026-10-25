module

public import DirectedCycles.LocalToLocalDoubledCurveRealization
public import DirectedCycles.LocalToLocalClosedScaledExponentLimit
public import DirectedCycles.LocalNestedSegmentComparison
public import DirectedCycles.BoundedSignedRatioLimit
public import DirectedCycles.LocalUniformSegmentMembership
public import DirectedCycles.LocalExponentialRadialLaw

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    {Q : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) Q)

/-- A corrected family of actual local power segments stays inside the source
through every old exit index. Compactness supplies real limits of both
variable exponents, the exact local model laws identify their images, and
the signed rounding bound places those images strictly in the inner ball. -/
theorem local_lie_target_corrected_model_control
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (B : ∀ i, Set (G i)) (g u : ∀ i, G i) (N₁ M₁ N₀ M₀ : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (g i) (M₁ i))
    (q : ∀ i, (L i).PowerSegment (u i) (M₀ i))
    (hN₁ : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N₁ i)
    (hN₀ : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N₀ i)
    (hM₁ : ∀ᶠ i in (U : Filter ι), 2*N₁ i ≤ M₁ i)
    (hM₀ : ∀ᶠ i in (U : Filter ι), 4*N₀ i ≤ M₀ i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ B i, (L i).inv x ∈ B i)
    (hp : ∀ᶠ i in (U : Filter ι), ∀ n < N₁ i, (p i).power n ∈ B i)
    (hq : ∀ᶠ i in (U : Filter ι), ∀ n < N₀ i, (q i).power n ∈ B i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H) (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G B, π.toFun z ∈ V)
    (φ ψ : ℝ → H)
    (hφ : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L g N₁ M₁ p t))
    (hψ : ∀ t : ℝ, |t| ≤ 1 → ψ t = π.toFun (localScaledPower U G L u N₀ M₀ q t))
    (hψadd : ∀ s t : ℝ, |s|+|t| ≤ 2 → Q.mulRel (ψ s) (ψ t) (ψ (s+t)))
    {r δ t t' : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (X : E) (hX : ‖X‖ ≤ (1001/1000)*r)
    (hφexp : ∀ s : ℝ, |s| ≤ 1 → φ s = D.chart ((t*s) • X))
    (hψexp : ∀ s : ℝ, |s| ≤ 2 → ψ s = D.chart ((t'*s) • X))
    (hwide : (|t|+2*|t'|)*‖X‖ < D.radius)
    (hinner : ∀ z, π.toFun z ∈ D.chart '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G B)
    (m : ι → ℤ) (s : ∀ i, ℕ → G i)
    (hm : ∀ᶠ i in (U : Filter ι), (m i).natAbs*N₁ i ≤ 2*N₀ i)
    (hs : ∀ᶠ i in (U : Filter ι), ∀ n ≤ N₁ i,
      (L i).mulRel ((p i).power n) ((q i).signedPower (-(m i)*(n : ℤ))) (s i n))
    (herr : ∀ᶠ i in (U : Filter ι), ∀ n ≤ N₁ i,
      |(t/(N₁ i : ℝ)-(m i : ℝ)*t'/(N₀ i : ℝ))*(n : ℝ)| ≤ (121/200)*δ) :
    ∀ᶠ i in (U : Filter ι), ∀ n ≤ N₁ i, s i n ∈ B i := by
  apply local_uniform_segment_membership U G B s N₁
  intro n hn
  obtain ⟨a,ha,hla⟩ := bounded_nat_ratio_ultralimit U N₁ n hn
  let k : ι → ℤ := fun i => -(m i)*(n i : ℤ)
  have hk : ∀ᶠ i in (U : Filter ι), (k i).natAbs ≤ 2*N₀ i := by
    filter_upwards [hn,hm] with i hni hmi
    dsimp only [k]
    simp only [Int.natAbs_mul,Int.natAbs_neg,Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left (m i).natAbs hni).trans hmi
  obtain ⟨b,hb,hlb⟩ := bounded_signed_ratio_ultralimit U N₀ k 2 (hN₀ 0) hk
  have hmap₁ := local_to_local_model_scaled_exponent_limit_closed U G L Q hd hr B g N₁ M₁ p
    (fun i => (n i : ℤ)) a hN₁ hM₁ hi hp
    (hn.mono fun i h => by simpa only [Int.natAbs_natCast] using h)
    (by rw [abs_of_nonneg ha.1]; exact ha.2)
    (by simpa only [Int.cast_natCast] using hla) π V hNSS himage
  simp only [LocalGroupAlgebra.PowerSegment.signedPower_nat] at hmap₁
  rw [← hφ a (by rw [abs_of_nonneg ha.1]; exact ha.2)] at hmap₁
  have hmap₀ := local_to_local_model_doubled_exponent_limit U G L Q hd hr B u N₀ M₀ q k b
    hN₀ hM₀ hi hq hk hb hlb π V hNSS himage ψ hψadd hψ
  have hrel : (localUltraAlgebra (U : Filter ι) G L).mulRel
      (localUltraMk (U : Filter ι) G (fun i => (p i).power (n i)))
      (localUltraMk (U : Filter ι) G (fun i => (q i).signedPower (k i)))
      (localUltraMk (U : Filter ι) G (fun i => s i (n i))) := by
    apply (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2
    filter_upwards [hn,hs] with i hni hsi
    exact hsi (n i) hni
  have he := π.map_mul hrel
  rw [hmap₁,hmap₀,hφexp a (by rw [abs_of_nonneg ha.1]; exact ha.2),hψexp b hb] at he
  have hsize : (|t*a|+|t'*b|)*‖X‖ < D.radius := by
    have haa : |a| ≤ 1 := by rw [abs_of_nonneg ha.1]; exact ha.2
    have h1 := mul_le_mul_of_nonneg_left haa (abs_nonneg t)
    have h2 := mul_le_mul_of_nonneg_left hb (abs_nonneg t')
    have hsum : |t| * |a|+|t'| * |b| ≤ |t|+2*|t'| := by
      simpa only [mul_one,Nat.cast_ofNat,mul_comm |t'| 2] using add_le_add h1 h2
    rw [abs_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right hsum (norm_nonneg X)).trans_lt hwide
  have heq := Q.unique he (D.radial_of_norm X (t*a) (t'*b) hsize)
  have hlim : Filter.Tendsto
      (fun i => |t*((n i : ℝ)/(N₁ i : ℝ))+t'*((k i : ℝ)/(N₀ i : ℝ))|)
      (U : Filter ι) (𝓝 |t*a+t'*b|) := ((hla.const_mul t).add (hlb.const_mul t')).abs
  have hbound : |t*a+t'*b| ≤ (121/200)*δ := by
    apply isClosed_Iic.mem_of_tendsto hlim
    filter_upwards [hn,herr] with i hni hei
    have hh := hei (n i) hni
    change |t*((n i : ℝ)/(N₁ i : ℝ))+t'*((k i : ℝ)/(N₀ i : ℝ))| ≤ (121/200)*δ
    have hecoef : t*((n i : ℝ)/(N₁ i : ℝ))+t'*((k i : ℝ)/(N₀ i : ℝ)) =
        (t/(N₁ i : ℝ)-(m i : ℝ)*t'/(N₀ i : ℝ))*(n i : ℝ) := by
      dsimp only [k]
      push_cast
      ring
    rw [hecoef]
    exact hh
  apply hinner
  rw [heq]
  refine ⟨(t*a+t'*b) • X,?_,rfl⟩
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
  have hh := mul_le_mul hbound hX (norm_nonneg X) (show 0 ≤ (121/200)*δ by positivity)
  have hp0 : 0 < δ*r := mul_pos hδ hr0
  nlinarith
end DirectedCycles
