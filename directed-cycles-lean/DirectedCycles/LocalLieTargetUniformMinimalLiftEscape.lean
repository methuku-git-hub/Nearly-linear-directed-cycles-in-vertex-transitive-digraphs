module

public import DirectedCycles.LocalLieTargetComponentLeastLiftNoInfinitesimal
public import DirectedCycles.LocalLargeIndexModels
public import DirectedCycles.FiniteUniformDomination
public import DirectedCycles.LocalZeroEscapeSubgroup

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Finite (G i)] (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    {Q : LocalGroupAlgebra H} (Y : LocalExponentialData (E := E) Q)

/-- Uniform escape-controlled lifting for the actual finite central
quotients and supplied compatible models. Finite minimization and restriction
to a large set derive one bound from the no-infinitesimal theorem. No quotient
source NSS or uniform lifting bound is assumed. -/
theorem local_lie_target_uniform_minimal_lift_escape_bound
    (hQ : LocalGroupSmoothness (E := E) Q)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {Ka Kb : ℕ} (A B : ∀ i, Finset (G i))
    (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (hB : ∀ i, IsLocalFiniteApproximateGroup (L i) Kb (B i))
    (hBA : ∀ i, (B i : Set (G i)) ⊆ A i)
    (hANSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (u : ∀ i, G i) (Nu : ι → ℕ)
    (pu : ∀ i, (L i).PowerSegment (u i) (2*Nu i))
    (hNu2 : ∀ i, 2 ≤ Nu i)
    (hup : ∀ i, ∀ n < Nu i, (pu i).power n ∈ A i)
    (hue : ∀ i, (pu i).power (Nu i) ∉ A i)
    (hu : ∀ i, u i ∈ B i)
    (hu1 : ∀ i, u i ≠ (L i).one)
    (hunorm : ∀ i, (L i).escapeNorm (A i : Set (G i)) (u i) = 1/(Nu i : ℝ))
    (humin : ∀ i, ∀ x ∈ A i, x ≠ (L i).one →
      (L i).escapeNorm (A i : Set (G i)) (u i) ≤ (L i).escapeNorm (A i : Set (G i)) x)
    (hNu : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < Nu i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H)
    (htrap : ∀ O : Set H, O ∈ 𝓝 Q.one → ∃ k : ℕ, 1 ≤ k ∧
      ∀ x : H, (∀ n ≤ k, Q.PowerIn V x n) → x ∈ O) (hVNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    {r δ : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 10*r < Y.radius)
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*r))
    (hAs : ∀ z, π.toFun z ∈ Y.chart '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hBo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))),
      π.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*δ*r))
    (hBs : ∀ z, π.toFun z ∈ Y.chart '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (φ : ℝ → H) (hφ0 : φ 0 = Q.one) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (φ s) (φ t) (φ (s+t)))
    (hφform : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u Nu (fun i => 2*Nu i) pu t))
    (P : ∀ i, Set (G i)) (hPeq : ∀ i, P i = (pu i).shortSignedSet (Nu i))
    (D : ∀ i, (L i).CentralQuotientData (P i))
    (hBsmall : ∀ i, (B i : Set (G i)) ⊆ (D i).small)
    (hB8small : ∀ i, (L i).wordPower (B i : Set (G i)) 8 ⊆ (D i).small)
    (hcentral : ∀ i, ∀ x ∈ B i, (L i).Commute x (u i))
    {T : Type*} (M : LocalGroupAlgebra T)
    (Ψ : LocalGroupHom (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra)) M)
    (hkernel : ∀ a : ∀ i, (D i).small,
      Ψ.toFun (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i))) = M.one →
        π.toFun (localUltraMk (U : Filter ι) G (fun i => (a i).val)) ∈
          π.toFun '' localUltraSet (U : Filter ι) G P)
    (Vq : Set T)
    (hqNSS : ∀ x : T, ∀ q : M.PowerSequence x, (∀ n, q.power n ∈ Vq) → x = M.one)
    (hqimage : ∀ z ∈ localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
        (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)),
      Ψ.toFun z ∈ Vq) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι), ∀ x : (D i).small, x.val ∈ B i →
      (∀ z : (D i).small, z.val ∈ B i → (D i).project z = (D i).project x →
        (L i).escapeNorm (B i : Set (G i)) x.val ≤ (L i).escapeNorm (B i : Set (G i)) z.val) →
      (L i).escapeNorm (B i : Set (G i)) x.val ≤
        C*(D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) ((D i).project x) := by
  classical
  let MinLift : ∀ i, (D i).small → Prop := fun i x =>
    ∀ z : (D i).small, z.val ∈ B i → (D i).project z = (D i).project x →
      (L i).escapeNorm (B i : Set (G i)) x.val ≤ (L i).escapeNorm (B i : Set (G i)) z.val
  let S : ∀ i, Finset (D i).small := fun i => ((B i).subtype (· ∈ (D i).small)).filter (MinLift i)
  let a : ∀ i, (D i).small → ℝ := fun i x => (L i).escapeNorm (B i : Set (G i)) x.val
  let b : ∀ i, (D i).small → ℝ := fun i x =>
    (D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) ((D i).project x)
  have hqone : ∀ i, (D i).algebra.one ∈ (D i).finiteImage (B i) := by
    intro i
    apply Finset.mem_image.mpr
    exact ⟨⟨(L i).one,(D i).one_mem⟩,by simpa only [Finset.mem_subtype] using (hB i).one_mem,
      (D i).projectionHom.map_one⟩
  have hb : ∀ i, ∀ x ∈ S i, 0 ≤ b i x :=
    fun i x _ => (D i).algebra.escapeNorm_nonneg (hqone i) ((D i).project x)
  have hexclude : ∀ x : ∀ i, (D i).small,
      (∀ᶠ i in (U : Filter ι), x i ∈ S i ∧ 0 < a i (x i)) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι), b i (x i) < ε*a i (x i)) → False := by
    intro x hx hsmall
    let s : Set ι := {i | (x i).val ∈ B i ∧ (x i).val ≠ (L i).one ∧ MinLift i (x i)}
    have hs : s ∈ U := by
      filter_upwards [hx] with i hi
      have hf := Finset.mem_filter.mp hi.1
      refine ⟨by simpa only [Finset.mem_subtype] using hf.1,?_,hf.2⟩
      intro he
      have hz : a i (x i) = 0 := by dsimp only [a]; rw [he,(L i).escapeNorm_one (hB i).one_mem]
      linarith [hi.2]
    let U' := localLargeIndexUltrafilter U s hs
    let G' := fun j : s => G j.val
    let L' := fun j : s => L j.val
    let e := localLargeIndexExtend U s hs G L
    let π' := π.comp e
    let Ψ' := Ψ.comp (localLargeIndexExtend U s hs (fun i => (D i).Carrier) (fun i => (D i).algebra))
    have himage' : ∀ z ∈ localUltraSet (U' : Filter s) G' (fun j => (A j.val : Set (G' j))), π'.toFun z ∈ V :=
      fun z hz => himage (e.toFun z) ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)
    have hAo' : ∀ z ∈ localUltraSet (U' : Filter s) G' (fun j => (A j.val : Set (G' j))),
        π'.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*r) :=
      fun z hz => hAo (e.toFun z) ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)
    have hAs' : ∀ z, π'.toFun z ∈ Y.chart '' Metric.ball (0 : E) r →
        z ∈ localUltraSet (U' : Filter s) G' (fun j => (A j.val : Set (G' j))) :=
      fun z hz => (localLargeIndex_extend_mem U s hs G L _ z).1 (hAs (e.toFun z) hz)
    have hBo' : ∀ z ∈ localUltraSet (U' : Filter s) G' (fun j => (B j.val : Set (G' j))),
        π'.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*δ*r) :=
      fun z hz => hBo (e.toFun z) ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)
    have hBs' : ∀ z, π'.toFun z ∈ Y.chart '' Metric.ball (0 : E) (δ*r) →
        z ∈ localUltraSet (U' : Filter s) G' (fun j => (B j.val : Set (G' j))) :=
      fun z hz => (localLargeIndex_extend_mem U s hs G L _ z).1 (hBs (e.toFun z) hz)
    have hφform' : ∀ t : ℝ, |t| ≤ 1 → φ t = π'.toFun
        (localScaledPower U' G' L' (fun j => u j.val) (fun j => Nu j.val)
          (fun j => 2*Nu j.val) (fun j => pu j.val) t) := by
      intro t ht
      change φ t = π.toFun (e.toFun _)
      rw [localLargeIndex_extend_scaledPower U s hs G L u Nu (fun i => 2*Nu i) pu t]
      exact hφform t ht
    have hkernel' := localLargeIndex_component_kernel U s hs G L Q M P D π Ψ hkernel
    have hqimage' : ∀ z ∈ localUltraSet (U' : Filter s) (fun j => (D j.val).Carrier)
        (fun j => ((D j.val).finiteImage (B j.val) : Set (D j.val).Carrier)), Ψ'.toFun z ∈ Vq := by
      intro z hz
      apply hqimage
      exact (localLargeIndex_extend_mem U s hs (fun i => (D i).Carrier) (fun i => (D i).algebra)
        (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)) z).2 hz
    exact local_lie_target_least_lift_no_infinitesimal_ratio_components U' G' L' Y hQ (fun j => hd j.val) (fun j => hr j.val)
      (fun j => A j.val) (fun j => B j.val) (fun j => hA j.val) (fun j => hB j.val)
      (fun j => hBA j.val) (fun j => hANSS j.val) (fun j => u j.val) (fun j => (x j.val).val)
      (fun j => Nu j.val) (fun j => pu j.val) (fun j => hNu2 j.val) (fun j => hup j.val) (fun j => hue j.val)
      (fun j => hu j.val) (fun j => j.property.1) (fun j => hu1 j.val) (fun j => j.property.2.1)
      (fun j => hunorm j.val) (fun j => humin j.val)
      (fun n => (localLargeIndex_eventually U s hs (fun i => n < Nu i)).2 (hNu n))
      π' V htrap hVNSS himage' hr0 hδ hδ1 hR hAo' hAs' hBo' hBs'
      φ hφ0 hφc hφadd hφform' (fun j => P j.val) (fun j => hPeq j.val) (fun j => D j.val)
      (fun j => hBsmall j.val) (fun j => hB8small j.val) (fun j => j.property.2.2)
      (fun j => hcentral j.val _ j.property.1)
      (fun ε hε => (localLargeIndex_eventually U s hs (fun i => b i (x i) < ε*a i (x i))).2 (hsmall ε hε))
      M Ψ' hkernel' Vq hqNSS hqimage'
  obtain ⟨C,hC,hbound⟩ := finite_uniform_domination_of_no_infinitesimal U (fun i => (D i).small)
    (fun i => ⟨(L i).one,(D i).one_mem⟩) S a b hb hexclude
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with i hi
  intro x hx hmin
  exact hi x (Finset.mem_filter.mpr ⟨by simpa only [Finset.mem_subtype] using hx,hmin⟩)
end DirectedCycles
