import DirectedCycles.LocalLieProgressionStatement
import DirectedCycles.LocalSmoothModelNormalization
import DirectedCycles.LocalLieTargetCentralReduction
import DirectedCycles.LocalCentralProgressionWindowCaller

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology Manifold ContDiff BigOperators
universe uι uG uH uE
namespace DirectedCycles

/-- The actual central quotient closes one normalized induction step.
Only the lower-dimensional instance of the induction assertion is used;
all central, quotient NSS, density and lift data are constructed here. -/
theorem local_normalized_progression_step
    {ι : Type uι} {G : ι → Type uG} [∀ i, Fintype (G i)]
    {U : Ultrafilter ι} {L : ∀ i, LocalGroupAlgebra (G i)}
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {H : Type uH} {E : Type uE} [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [Nontrivial E] [ChartedSpace E H] [IsManifold 𝓘(ℝ,E) ∞ H]
    {Q : LocalGroupAlgebra H} (Y : LocalExponentialData (E := E) Q)
    (hQ : LocalGroupSmoothness (E := E) Q) (hdQ : Q.DivisionClosed) (hrQ : Q.Reversible)
    {A : ∀ i, Finset (G i)} {Ka : ℕ}
    (hA : ∀ i, IsStrongLocalFiniteApproximateGroup (L i) Ka (A i))
    (hNSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (hne : ∀ i, ∃ g ∈ A i, g ≠ (L i).one)
    (M : LocalSmoothModelData U G L A Q) (hM : M.Normalized Y)
    (ih : ∀ d' < Module.finrank ℝ E, LocalLieProgressionStatement.{uι,uG,uH,uE} d') :
    HasLargeLocalProgressions (U : Filter ι) G L (fun i => (A i : Set (G i)))
      (fun i => (A i).card) := by
  classical
  obtain ⟨⟨ra,hra,hRa,hAo,hAs⟩,hVNSS,htrap⟩ := hM
  obtain ⟨τ,_hτ,_hτhalf,u,N,p,P,φ,hdata,hNu,_hφc,_hφ0,_hφadd,_hφ1,_hPimage,
    v,ℓ,_hv,_hℓ,hdim,T,_hTo,hTdiv,hTrev,hT2,hTlc,cs,hman,hsmooth,
    K,J,_hK,hJ,B,D,hB,hstrong,hcard,⟨C₀,hC₀,hescape⟩,Ψ,Vq,O,hVq,himage,
    _hqNSS,_hqtrap,hOo,hO1,hsmall,hthick,hsand,C,hC,hcontrol⟩ :=
    local_lie_target_central_reduction Y hQ hdQ hrQ U G L hd hr A hA hNSS hne
      M.map hra hRa hAo hAs M.compactSet M.compact hVNSS htrap M.image
      M.window M.window_open M.one_mem M.small M.thick M.sandwich
  let := hT2
  let := hTlc
  let := cs
  let := hman
  let : ∀ i, Fintype (D i).Carrier := fun i => Fintype.ofFinite _
  let Mq : LocalSmoothModelData U (fun i => (D i).Carrier) (fun i => (D i).algebra)
      (fun i => (D i).finiteImage (B i)) T.algebra := {
    map := Ψ
    compactSet := Vq
    compact := hVq
    image := fun z _ => himage z
    window := O
    window_open := hOo
    one_mem := hO1
    small := hsmall
    thick := by
      intro y hy
      obtain ⟨z,_hz,hzy⟩ := hthick hy
      exact ⟨z,hzy⟩
    sandwich := fun F O' hF hO' hFO _ => hsand F O' hF hO' hFO }
  have hq := ih (Module.finrank ℝ ℓ.ker) (by omega) ι (fun i => (D i).Carrier) U
    (fun i => (D i).algebra) (fun i => (hB i).2.2.2.2.2.2.1)
    (fun i => (hB i).2.2.2.2.2.2.2) T.Carrier ℓ.ker T.algebra hsmooth hTdiv hTrev
    (fun i => (D i).finiteImage (B i)) K
    (Filter.Eventually.of_forall (fun i => (hB i).2.2.2.2.2.1))
    (hcontrol.mono fun _ hi => hi.2) Mq rfl
  obtain ⟨r,c,Jq,hJq,Nq,hNq,hWq⟩ := hq
  obtain ⟨g,hquot⟩ := choose_local_progression_family (U : Filter ι) (fun i => (D i).Carrier)
    (fun i => (D i).algebra) (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier))
    Nq (fun i => ((D i).finiteImage (B i)).card) hWq
  obtain ⟨T',M',_hT',hM',hlength,hW⟩ := local_central_progression_family_from_windows
    (U : Filter ι) G L hd hr A B P D (fun i => (hA i).approximate) hJ hJq hC.le hC₀.le
    hstrong (fun i => (hB i).2.1) (fun i => (hB i).2.2.2.1) τ
    (fun i => (hB i).2.2.2.2.1) (fun i => (hdata i).2.2.2.2.2.2.2.2.2)
    (hcontrol.mono fun _ hi => hi.1) u N p (fun i => (hdata i).1)
    (fun i => (hdata i).2.2.1) hescape hNSS (fun i => (hdata i).2.2.2.1)
    (fun i => (hdata i).2.2.2.2.2.2.1) (fun i => (hdata i).2.2.2.2.2.2.2.1)
    hcard g Nq hNq hNu hquot
  exact ⟨r+1,c+1,M',hM',fun i j => (Fin.lastCases (N i) (Nq i) j)/T',hlength,hW⟩
end DirectedCycles
