import DirectedCycles.LocalSmoothModelStrongWindows
import DirectedCycles.LocalExponentialBallTopology

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalSmoothModelData

/-- Binary domains, compact control and the good-model sandwich suffice
to construct a dense strong submodel. The original finite source need not
already be an approximate group. -/
theorem exists_strong_submodel {ι H E : Type*}
    [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E H]
    {U : Ultrafilter ι} {G : ι → Type*} [∀ i, Fintype (G i)]
    {L : ∀ i, LocalGroupAlgebra (G i)} {A : ∀ i, Finset (G i)}
    {Q : LocalGroupAlgebra H} (M : LocalSmoothModelData U G L A Q)
    (Y : LocalExponentialData (E := E) Q) (hQ : LocalGroupSmoothness (E := E) Q)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (hA1 : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i)
    (hAi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hAdom : ∀ᶠ i in (U : Filter ι), (L i).AllProductsDefined (A i : Set (G i)) 2) :
    ∃ K J : ℕ, 1 ≤ K ∧ 1 ≤ J ∧ ∃ B : ∀ i, Finset (G i),
      (∀ᶠ i in (U : Filter ι), B i ⊆ A i ∧ (A i).card ≤ J*(B i).card ∧
        IsStrongLocalFiniteApproximateGroup (L i) K (B i)) ∧
      Nonempty (LocalSmoothModelData U G L B Q) := by
  let L' := localUltraAlgebra (U : Filter ι) G L
  let A' := localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
  have hone : L'.one ∈ A' := (localUltraMk_mem_iff (U : Filter ι) G _ _).2 hA1
  have hinv : ∀ x ∈ A', L'.inv x ∈ A' := (localUltra_inv_closed_iff U G L _).2 hAi
  have hdom := (localUltra_allProductsDefined_iff U G L _ 2).2 hAdom
  have hbinary : ∀ x ∈ A', ∀ y ∈ A', L'.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hdom [x,y] (by simp) (by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl
      · exact hx
      · exact hy)
    exact ⟨z,(LocalGroupAlgebra.Product.pair_iff L' x y z).1 hz⟩
  obtain ⟨K,R,hK,hR,hwin⟩ := large_strong_local_groups_from_local_lie_model Y hQ U G L
    (localUltraAlgebra_divisionClosed (U : Filter ι) G L hd)
    (localUltraAlgebra_reversible (U : Filter ι) G L hr) M.map A hone hinv hbinary
    M.compactSet M.compact (by rintro _ ⟨z,hz,rfl⟩; exact M.image z hz)
    M.window (M.window_open.mem_nhds M.one_mem) M.small M.sandwich
  obtain ⟨Rs,hRs,hsand⟩ := Y.ball_sandwich M.window (M.window_open.mem_nhds M.one_mem)
  let r := min R (min Rs Y.radius)/2
  have hr0 : 0 < r := div_pos (lt_min hR (lt_min hRs Y.radius_pos)) (by norm_num)
  have hrR : r < R := by dsimp only [r]; linarith [min_le_left R (min Rs Y.radius)]
  have hrRs : r < Rs := by
    dsimp only [r]
    linarith [min_le_right R (min Rs Y.radius),min_le_left Rs Y.radius]
  have hrY : r ≤ Y.radius := by
    dsimp only [r]
    linarith [min_le_right R (min Rs Y.radius),min_le_right Rs Y.radius,Y.radius_pos]
  obtain ⟨B,J,hJ,hBin,_hBout,hgood⟩ := hwin r hr0 hrR
  have hBA := (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).2
    (hgood.mono fun _ hi => hi.1)
  let S := Y.chart '' Metric.ball (0 : E) r
  have hSM : S ⊆ M.window :=
    (Set.image_mono (Metric.ball_subset_ball (by linarith))).trans (hsand r hr0 hrRs).2.2.2.1
  have hS1 : Q.one ∈ S := ⟨0,by simpa only [Metric.mem_ball,dist_self] using hr0,Y.zero⟩
  refine ⟨K,J,hK,hJ,B,hgood,⟨M.shrink M.compactSet S M.compact
    (fun z hz => M.image z (hBA hz)) (Y.ball_open hrY) hS1 hSM ?_⟩⟩
  exact fun _ hz => hBin ((Set.image_mono Metric.ball_subset_closedBall) hz)
end DirectedCycles.LocalSmoothModelData
