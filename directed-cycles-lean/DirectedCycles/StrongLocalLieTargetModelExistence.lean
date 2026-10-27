module

public import DirectedCycles.LocalLieTargetSandwichApproximate
public import DirectedCycles.LocalLieTargetModelTrapping
public import DirectedCycles.LocalLieTargetInternalWindows
public import DirectedCycles.LocalLieModelWordDomains
public import DirectedCycles.LocalStrongFiniteTransfer

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] {Q : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) Q)

/-- A genuine smooth local Lie model with the internal sandwich property constructs
arbitrarily small strong finite source approximate groups with one uniform
constant. Model existence remains a separate theorem, not an axiom here. -/
theorem strong_local_groups_from_local_lie_model
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (hd : (localUltraAlgebra (U : Filter ι) G L).DivisionClosed)
    (hr : (localUltraAlgebra (U : Filter ι) G L).Reversible)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (A₀ : Set (LocalUltraproduct (U : Filter ι) G))
    (hA₀ : (localUltraAlgebra (U : Filter ι) G L).one ∈ A₀)
    (hdom : ∀ x ∈ A₀, ∀ y ∈ A₀, (localUltraAlgebra (U : Filter ι) G L).Defined x y)
    (W : Set H) (hW : W ∈ 𝓝 Q.one)
    (hsmall : π.toFun ⁻¹' W ⊆ A₀)
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V → V ⊆ W →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' V) :
    ∃ K : ℕ, ∃ R : ℝ, 1 ≤ K ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ A : ∀ i, Finset (G i),
        localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆ A₀ ∧
        π.toFun ⁻¹' (D.chart '' Metric.closedBall (0 : E) r) ⊆
          localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆
          π.toFun ⁻¹' (D.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
        ∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (A i) := by
  let M := localUltraAlgebra (U : Filter ι) G L
  obtain ⟨K,Ra,hK,hRa,ha⟩ := exists_uniform_local_lie_sandwich_approximate
    (G := LocalUltraproduct (U : Filter ι) G) D
  let T := 1000*K^3
  have hT : 1 ≤ T := by
    dsimp only [T]
    have : 0 < K := by omega
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  let N := max 200 (9*T)
  have hN200 : 200 ≤ N := le_max_left _ _
  have hN9 : 9*T ≤ N := le_max_right _ _
  obtain ⟨Rt,hRt,ht⟩ := exists_local_lie_strong_trapping_windows D T hT
  obtain ⟨Rd,hRd,hdomains⟩ := exists_local_lie_model_word_domain_radius D M A₀ hA₀ hdom π W hW
    (fun _ hx => hsmall hx) N
  obtain ⟨Ri,hRi,hi⟩ := exists_local_to_local_internal_exponential_windows D U G L π W hW hsandwich
  let R := min Ri (min Ra (min Rt Rd))
  have hR : 0 < R := lt_min hRi (lt_min hRa (lt_min hRt hRd))
  refine ⟨K,R,hK,hR,?_⟩
  intro r hrpos hrR
  have hrRi : r < Ri := hrR.trans_le (min_le_left _ _)
  have hrRa : r < Ra := hrR.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrRt : r < Rt := hrR.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrRd : r < Rd := hrR.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let s := r/(10*(T : ℝ))
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < T := by linarith
  have hs : 0 < s := div_pos hrpos (by positivity)
  have hscale : 10*(T : ℝ)*s = r := by dsimp only [s]; field_simp
  have hsr : s < r := by nlinarith
  have hsouter : (1001/1000 : ℝ)*s ≤ r := by nlinarith
  obtain ⟨A,hAi,hAin,hAout⟩ := hi r hrpos hrRi
  obtain ⟨S,hSi,hSin,hSout⟩ := hi s hs (hsr.trans hrRi)
  let A' := localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
  let S' := localUltraSet (U : Filter ι) G (fun i => (S i : Set (G i)))
  have hAimage : π.toFun '' A' ⊆ D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r) := by
    rintro _ ⟨x,hx,rfl⟩
    exact Set.image_mono Metric.ball_subset_closedBall (hAout hx)
  have hSimage : π.toFun '' S' ⊆ D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*s) := by
    rintro _ ⟨x,hx,rfl⟩
    exact Set.image_mono Metric.ball_subset_closedBall (hSout hx)
  have hSA : S' ⊆ A' := by
    intro x hx
    apply hAin
    exact Set.image_mono (Metric.closedBall_subset_closedBall hsouter) (hSimage ⟨x,hx,rfl⟩)
  have hAone : M.one ∈ A' := by
    apply hAin
    exact ⟨0,by simpa only [Metric.mem_closedBall,dist_self] using hrpos.le,
      by simpa only [D.zero,M] using π.map_one.symm⟩
  have hAi' : ∀ x ∈ A', M.inv x ∈ A' :=
    (localUltra_inv_closed_iff U G L _).2 (Filter.Eventually.of_forall hAi)
  have hSi' : ∀ x ∈ S', M.inv x ∈ S' :=
    (localUltra_inv_closed_iff U G L _).2 (Filter.Eventually.of_forall hSi)
  obtain ⟨hAA₀,hAdom,_⟩ := hdomains r hrpos hrRd A' hAimage
  have happrox := ha r hrpos hrRa M hd hr π A' hAone hAi'
    (hAdom.mono M (Set.Subset.refl _) hN200) hAimage (by
      intro x _ hx
      exact hAin (Set.image_mono Metric.ball_subset_closedBall hx))
  obtain ⟨hQdom,hQA,hfirst,hsecond⟩ := local_lie_target_model_trapping D M hr π hK (by omega) hN9
    (ht r hrpos hrRt) A' S' hAone hAi' hSA hAdom hAimage hSimage
    (by intro x _ hx; exact hAin (Set.image_mono Metric.ball_subset_closedBall hx))
    (by intro x _ hx; exact hSin (Set.image_mono Metric.ball_subset_closedBall hx))
  refine ⟨A,hAA₀,hAin,hAout,?_⟩
  exact localStrongFiniteApproximate_eventually U G L A (fun i => (S i : Set (G i)))
    happrox hSi' hQdom hQA hfirst hsecond
end DirectedCycles
