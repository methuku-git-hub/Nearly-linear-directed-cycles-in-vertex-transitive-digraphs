import DirectedCycles.StrongLocalLieModelExistence
import DirectedCycles.LocalCompactModelCover
import DirectedCycles.LocalFiniteCoverTransfer

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [LieGroup 𝓘(ℝ,E) ∞ H]

/-- The constructed exponential source neighbourhoods are large strong
finite approximate groups. Uniform density is proved by an actual finite
local cover and component cardinal counting. This requires a supplied
genuine global Lie model and does not assert its existence. -/
theorem large_strong_local_groups_from_lie_model
    (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
    (L : ∀ i, LocalGroupAlgebra (G i))
    (hd : (localUltraAlgebra (U : Filter ι) G L).DivisionClosed)
    (hr : (localUltraAlgebra (U : Filter ι) G L).Reversible)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (A : ∀ i, Finset (G i))
    (hA1 : (localUltraAlgebra (U : Filter ι) G L).one ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hAi : ∀ x ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      (localUltraAlgebra (U : Filter ι) G L).inv x ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hdom : ∀ x ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      ∀ y ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
        (localUltraAlgebra (U : Filter ι) G L).Defined x y)
    (C : Set H) (hC : IsCompact C)
    (hAC : π.toFun '' localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆ C)
    (W : Set H) (hW : W ∈ 𝓝 (1 : H))
    (hsmall : π.toFun ⁻¹' W ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V → V ⊆ W →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' V) :
    ∃ K : ℕ, ∃ R : ℝ, 1 ≤ K ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ B : ∀ i, Finset (G i), ∃ J : ℕ, 1 ≤ J ∧
        π.toFun ⁻¹' ((lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) r) ⊆
          localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆
          π.toFun ⁻¹' ((lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
        ∀ᶠ i in (U : Filter ι), B i ⊆ A i ∧ (A i).card ≤ J*(B i).card ∧
          IsStrongLocalFiniteApproximateGroup (L i) K (B i) := by
  let : IsTopologicalGroup H := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let M := localUltraAlgebra (U : Filter ι) G L
  let A' := localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
  obtain ⟨K,R₁,hK,hR₁,hstrong⟩ := strong_local_groups_from_lie_model (E := E) U G L hd hr π A'
    hA1 hdom W hW hsmall hsandwich
  obtain ⟨R₂,hR₂,hopen⟩ := lie_exponential_small_ball_open (G := H) (E := E)
  refine ⟨K,min R₁ R₂,hK,lt_min hR₁ hR₂,?_⟩
  intro r hrpos hrR
  obtain ⟨B,hBA,hBin,hBout,hBs⟩ := hstrong r hrpos (hrR.trans_le (min_le_left _ _))
  let B' := localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i)))
  let V := (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r
  have hV : V ∈ 𝓝 (1 : H) :=
    (hopen r (hrR.trans_le (min_le_right _ _)).le).mem_nhds
      ⟨0,by simpa only [Metric.mem_ball,dist_self] using hrpos,lieExponential_zero⟩
  obtain ⟨X,_,hcover⟩ := local_finite_cover_of_compact_model M hd π A' B' hAi hdom C hC hAC V hV
    (fun _ hx => hBin (Set.image_mono Metric.ball_subset_closedBall hx))
  obtain ⟨J,hJ,hcard⟩ := local_density_of_internal_finite_cover U G L A B ⟨X,hcover⟩
  have hsub := (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).1 hBA
  refine ⟨B,J,hJ,hBin,hBout,?_⟩
  filter_upwards [hsub,hcard,hBs] with i hi hci hsi
  exact ⟨hi,hci,hsi⟩
end DirectedCycles
