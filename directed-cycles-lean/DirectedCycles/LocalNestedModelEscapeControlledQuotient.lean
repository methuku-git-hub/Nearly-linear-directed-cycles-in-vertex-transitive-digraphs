module

public import DirectedCycles.LocalUniformEscapeControlledQuotient
public import DirectedCycles.LocalLargeIndexModels
public import DirectedCycles.LocalQuotientEscapeControlledLifts

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Finite (G i)] (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- Nested compatible models give actual uniformly controlled quotient
lifts and NSS quotient components. Membership of the selected central
generator in the inner source is proved from its unbounded outer exit time;
it is not added as an assumption on every component. -/
theorem local_escape_controlled_quotient_from_nested_models
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
    (hu1 : ∀ i, u i ≠ (L i).one)
    (hunorm : ∀ i, (L i).escapeNorm (A i : Set (G i)) (u i) = 1/(Nu i : ℝ))
    (humin : ∀ i, ∀ x ∈ A i, x ≠ (L i).one →
      (L i).escapeNorm (A i : Set (G i)) (u i) ≤ (L i).escapeNorm (A i : Set (G i)) x)
    (hNu : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < Nu i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V) (hVNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    {R r δ : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : (1001/1000)*r < R)
    (hinj : Set.InjOn (lieExponential (G := H) (E := E)) (Metric.ball 0 R))
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*r))
    (hAs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hBo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))),
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*δ*r))
    (hBs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (φ : ℝ → H) (hφ0 : φ 0 = 1) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
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
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι),
      (∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small, x.val ∈ B i ∧ (D i).project x = y ∧
        (L i).escapeNorm (B i : Set (G i)) x.val ≤
          C*(D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) y) ∧
      (D i).algebra.IsNSS ((D i).finiteImage (B i) : Set (D i).Carrier) := by
  have hkill := local_model_kills_generator U G L (fun i => (A i : Set (G i))) u Nu
    (fun i => 2*Nu i) pu hNu (Filter.Eventually.of_forall fun i => by omega)
    (Filter.Eventually.of_forall hup) π V hVNSS himage
  have hu : ∀ᶠ i in (U : Filter ι), u i ∈ B i :=
    (localUltraMk_mem_iff (U : Filter ι) G (fun i => (B i : Set (G i))) u).1
      (hBs _ ⟨0,by simpa only [Metric.mem_ball,dist_self] using mul_pos hδ hr0,
        lieExponential_zero.trans hkill.symm⟩)
  let s : Set ι := {i | u i ∈ B i}
  have hs : s ∈ U := hu
  let U' := localLargeIndexUltrafilter U s hs
  let G' := fun j : s => G j.val
  let L' := fun j : s => L j.val
  let e := localLargeIndexExtend U s hs G L
  let π' := π.comp e
  let Ψ' := Ψ.comp (localLargeIndexExtend U s hs (fun i => (D i).Carrier) (fun i => (D i).algebra))
  have himage' : ∀ z ∈ localUltraSet (U' : Filter s) G' (fun j => (A j.val : Set (G' j))), π'.toFun z ∈ V :=
    fun z hz => himage (e.toFun z) ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)
  have hAo' : ∀ z ∈ localUltraSet (U' : Filter s) G' (fun j => (A j.val : Set (G' j))),
      π'.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*r) :=
    fun z hz => hAo (e.toFun z) ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)
  have hAs' : ∀ z, π'.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U' : Filter s) G' (fun j => (A j.val : Set (G' j))) :=
    fun z hz => (localLargeIndex_extend_mem U s hs G L _ z).1 (hAs (e.toFun z) hz)
  have hBo' : ∀ z ∈ localUltraSet (U' : Filter s) G' (fun j => (B j.val : Set (G' j))),
      π'.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*δ*r) :=
    fun z hz => hBo (e.toFun z) ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)
  have hBs' : ∀ z, π'.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U' : Filter s) G' (fun j => (B j.val : Set (G' j))) :=
    fun z hz => (localLargeIndex_extend_mem U s hs G L _ z).1 (hBs (e.toFun z) hz)
  have hφform' : ∀ t : ℝ, |t| ≤ 1 → φ t = π'.toFun
      (localScaledPower U' G' L' (fun j => u j.val) (fun j => Nu j.val)
        (fun j => 2*Nu j.val) (fun j => pu j.val) t) := by
    intro t ht
    change φ t = π.toFun (e.toFun _)
    rw [localLargeIndex_extend_scaledPower U s hs G L u Nu (fun i => 2*Nu i) pu t]
    exact hφform t ht
  have hkernel' := localLargeIndex_component_kernel U s hs G L (LocalGroupAlgebra.ofGroup H) M P D π Ψ hkernel
  have hqimage' : ∀ z ∈ localUltraSet (U' : Filter s) (fun j => (D j.val).Carrier)
      (fun j => ((D j.val).finiteImage (B j.val) : Set (D j.val).Carrier)), Ψ'.toFun z ∈ Vq := by
    intro z hz
    apply hqimage
    exact (localLargeIndex_extend_mem U s hs (fun i => (D i).Carrier) (fun i => (D i).algebra)
      (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)) z).2 hz
  obtain ⟨C,hC,hbound⟩ := local_uniform_escape_controlled_quotient U' G' L'
    (fun j => hd j.val) (fun j => hr j.val) (fun j => A j.val) (fun j => B j.val)
    (fun j => hA j.val) (fun j => hB j.val) (fun j => hBA j.val) (fun j => hANSS j.val)
    (fun j => u j.val) (fun j => Nu j.val) (fun j => pu j.val) (fun j => hNu2 j.val)
    (fun j => hup j.val) (fun j => hue j.val) (fun j => j.property) (fun j => hu1 j.val)
    (fun j => hunorm j.val) (fun j => humin j.val)
    (fun n => (localLargeIndex_eventually U s hs (fun i => n < Nu i)).2 (hNu n))
    π' V hV hVNSS himage' hr0 hδ hδ1 hR hinj hAo' hAs' hBo' hBs' φ hφ0 hφc hφadd hφform'
    (fun j => P j.val) (fun j => hPeq j.val) (fun j => D j.val) (fun j => hBsmall j.val)
    (fun j => hB8small j.val) (fun j => hcentral j.val) M Ψ' hkernel' Vq hqNSS hqimage'
  refine ⟨C,hC,?_⟩
  exact (localLargeIndex_eventually U s hs (fun i =>
    (∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small, x.val ∈ B i ∧ (D i).project x = y ∧
      (L i).escapeNorm (B i : Set (G i)) x.val ≤
        C*(D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier) y) ∧
    (D i).algebra.IsNSS ((D i).finiteImage (B i) : Set (D i).Carrier))).1 hbound
end DirectedCycles
