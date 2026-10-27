module

public import DirectedCycles.LocalSmoothModelStrongWindows
public import DirectedCycles.LocalExponentialBallTopology
public import DirectedCycles.SmoothLocalCompactNSS

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalSmoothModelData
variable {ι H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E H] {U : Ultrafilter ι} {G : ι → Type*}
    {L : ∀ i, LocalGroupAlgebra (G i)} {A : ∀ i, Finset (G i)}
    {Q : LocalGroupAlgebra H}

/-- The quantitative coordinate and compact trapping data required by the
central reduction, for the actual map of a good model. -/
def Normalized (M : LocalSmoothModelData U G L A Q)
    (Y : LocalExponentialData (E := E) Q) : Prop :=
  (∃ r : ℝ, 0 < r ∧ 10*r < Y.radius ∧
    (∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      M.map.toFun z ∈ Y.chart '' Metric.closedBall (0 : E) ((1001/1000)*r)) ∧
    (∀ z, M.map.toFun z ∈ Y.chart '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))) ∧
  (∀ x : H, ∀ p : Q.PowerSequence x, (∀ n, p.power n ∈ M.compactSet) → x = Q.one) ∧
  (∀ W : Set H, W ∈ 𝓝 Q.one → ∃ n : ℕ, 1 ≤ n ∧
    ∀ x : H, (∀ j ≤ n, Q.PowerIn M.compactSet x j) → x ∈ W)

theorem Normalized.restrict {M : LocalSmoothModelData U G L A Q}
    {Y : LocalExponentialData (E := E) Q} (h : M.Normalized Y)
    (s : Set ι) (hs : s ∈ U) : (M.restrict s hs).Normalized Y := by
  obtain ⟨⟨r,hr,hR,hout,hin⟩,hseq,htrap⟩ := h
  refine ⟨⟨r,hr,hR,?_,?_⟩,hseq,htrap⟩
  · intro z hz
    exact hout _ ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)
  · intro z hz
    exact (localLargeIndex_extend_mem U s hs G L _ z).1 (hin _ hz)

/-- Every actual smooth model has uniformly dense strong windows with all
the coordinate and NSS trapping data needed for a central reduction. -/
theorem exists_normalized_window [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ H]
    [∀ i, Fintype (G i)] (M : LocalSmoothModelData U G L A Q)
    (Y : LocalExponentialData (E := E) Q) (hQ : LocalGroupSmoothness (E := E) Q)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {Ka : ℕ} (hA : ∀ᶠ i in (U : Filter ι), IsLocalFiniteApproximateGroup (L i) Ka (A i)) :
    ∃ K J : ℕ, 1 ≤ K ∧ 1 ≤ J ∧ ∃ B : ∀ i, Finset (G i),
      (∀ᶠ i in (U : Filter ι), B i ⊆ A i ∧ (A i).card ≤ J*(B i).card ∧
        IsStrongLocalFiniteApproximateGroup (L i) K (B i)) ∧
      ∃ M' : LocalSmoothModelData U G L B Q, M'.Normalized Y := by
  obtain ⟨V,hVn,hVc,hVM,_hVnss,hseq,htrap⟩ :=
    smooth_local_group_compact_nss Q hQ (M.window_open.mem_nhds M.one_mem)
  obtain ⟨Rs,hRs,hsand⟩ := Y.ball_sandwich V hVn
  obtain ⟨K,R,hK,hR,hwin⟩ := M.large_strong_windows Y hQ hd hr hA
  let r := min R (min Rs Y.radius)/20
  have hr0 : 0 < r := div_pos (lt_min hR (lt_min hRs Y.radius_pos)) (by norm_num)
  have hrR : r < R := by dsimp only [r]; linarith [min_le_left R (min Rs Y.radius)]
  have hrRs : r < Rs := by
    dsimp only [r]
    linarith [min_le_right R (min Rs Y.radius),min_le_left Rs Y.radius]
  have hrY : 10*r < Y.radius := by
    dsimp only [r]
    linarith [min_le_right R (min Rs Y.radius),min_le_right Rs Y.radius,Y.radius_pos]
  obtain ⟨B,J,hJ,hBin,hBout,hgood⟩ := hwin r hr0 hrR
  have houtV := (hsand r hr0 hrRs).2.2.2.1
  let S := Y.chart '' Metric.ball (0 : E) r
  have hSo : IsOpen S := Y.ball_open (by linarith)
  have hS1 : Q.one ∈ S := ⟨0,by simpa only [Metric.mem_ball,dist_self] using hr0,Y.zero⟩
  have hSM : S ⊆ M.window :=
    (Set.image_mono (Metric.ball_subset_ball (by linarith))).trans (houtV.trans hVM)
  have himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))),
      M.map.toFun z ∈ V := fun z hz => houtV (hBout hz)
  have hsmall : M.map.toFun ⁻¹' S ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) :=
    fun _ hz => hBin ((Set.image_mono Metric.ball_subset_closedBall) hz)
  let M' := M.shrink V S hVc himage hSo hS1 hSM hsmall
  refine ⟨K,J,hK,hJ,B,hgood,M',⟨r,hr0,hrY,?_,?_⟩,hseq,htrap⟩
  · intro z hz
    exact (Set.image_mono Metric.ball_subset_closedBall) (hBout hz)
  · intro z hz
    exact hsmall hz
end DirectedCycles.LocalSmoothModelData
