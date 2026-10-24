import DirectedCycles.LocalSmoothModelData
import DirectedCycles.LargeStrongLocalLieTargetModelExistence

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalSmoothModelData
variable {ι H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E H] {U : Ultrafilter ι} {G : ι → Type*}
    [∀ i, Fintype (G i)] {L : ∀ i, LocalGroupAlgebra (G i)} {A : ∀ i, Finset (G i)}
    {Q : LocalGroupAlgebra H} (M : LocalSmoothModelData U G L A Q)

/-- The actual good model constructs uniformly strong small finite windows,
retaining exact inner/outer coordinates and uniform source density. -/
theorem large_strong_windows (D : LocalExponentialData (E := E) Q)
    (hQ : LocalGroupSmoothness (E := E) Q)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {Ka : ℕ} (hA : ∀ᶠ i in (U : Filter ι), IsLocalFiniteApproximateGroup (L i) Ka (A i)) :
    ∃ K : ℕ, ∃ R : ℝ, 1 ≤ K ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ B : ∀ i, Finset (G i), ∃ J : ℕ, 1 ≤ J ∧
        M.map.toFun ⁻¹' (D.chart '' Metric.closedBall (0 : E) r) ⊆
          localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆
          M.map.toFun ⁻¹' (D.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
        ∀ᶠ i in (U : Filter ι), B i ⊆ A i ∧ (A i).card ≤ J*(B i).card ∧
          IsStrongLocalFiniteApproximateGroup (L i) K (B i) := by
  let J := localUltraAlgebra (U : Filter ι) G L
  let S := localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
  have hS1 : J.one ∈ S := (localUltraMk_mem_iff (U : Filter ι) G _ _).2 (hA.mono fun _ h => h.one_mem)
  have hSi : ∀ x ∈ S, J.inv x ∈ S :=
    (localUltra_inv_closed_iff U G L _).2 (hA.mono fun _ h => h.inv_mem)
  have hdom : J.AllProductsDefined S 2 := (localUltra_allProductsDefined_iff U G L _ 2).2
    (hA.mono fun i h => h.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200))
  have hbinary : ∀ x ∈ S, ∀ y ∈ S, J.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hdom [x,y] (by simp) (by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl
      · exact hx
      · exact hy)
    exact ⟨z,(LocalGroupAlgebra.Product.pair_iff J x y z).1 hz⟩
  exact large_strong_local_groups_from_local_lie_model D hQ U G L
    (localUltraAlgebra_divisionClosed (U : Filter ι) G L hd)
    (localUltraAlgebra_reversible (U : Filter ι) G L hr) M.map A hS1 hSi hbinary
    M.compactSet M.compact (by rintro _ ⟨z,hz,rfl⟩; exact M.image z hz)
    M.window (M.window_open.mem_nhds M.one_mem) M.small M.sandwich
end DirectedCycles.LocalSmoothModelData
