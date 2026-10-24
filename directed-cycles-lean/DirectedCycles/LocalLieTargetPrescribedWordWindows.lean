import DirectedCycles.LargeStrongLocalLieTargetModelExistence
import DirectedCycles.LocalLieTargetWordEscapeWindows
import DirectedCycles.LocalFiniteWindowNormalization
import DirectedCycles.LocalDivision

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] {Q : LocalGroupAlgebra H} (X : LocalExponentialData (E := E) Q)

/-- Prescribed exponential neighbourhoods are constructed as actual finite
approximate groups at every index, with arbitrary long word domains, small
escape in the original set and uniform density. Exceptional indices are
normalized without changing the internal neighbourhood. -/
theorem local_lie_target_prescribed_word_windows
    (hQ : LocalGroupSmoothness (E := E) Q)
    (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
    (L : ∀ i, LocalGroupAlgebra (G i)) (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Finset (G i)) {Ka : ℕ} (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (C : Set H) (hC : IsCompact C)
    (hAC : π.toFun '' localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆ C)
    (W : Set H) (hW : W ∈ 𝓝 Q.one)
    (hsmall : π.toFun ⁻¹' W ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V → V ⊆ W →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' V)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∃ R : ℝ, 1 ≤ K ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ B : ∀ i, Finset (G i), ∃ J : ℕ, 1 ≤ J ∧
        π.toFun ⁻¹' (X.chart '' Metric.closedBall (0 : E) r) ⊆
          localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆
          π.toFun ⁻¹' (X.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
        (∀ i, IsLocalFiniteApproximateGroup (L i) K (B i) ∧ B i ⊆ A i ∧
          (L i).AllProductsDefined (B i : Set (G i)) m ∧
          ∀ n ≤ m, ∀ x ∈ (L i).wordPower (B i : Set (G i)) n, (L i).escapeNorm (A i : Set (G i)) x < ε) ∧
        (∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (B i)) ∧
        ∀ᶠ i in (U : Filter ι), (A i).card ≤ J*(B i).card := by
  let M := localUltraAlgebra (U : Filter ι) G L
  let A' := localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
  have hA1 : M.one ∈ A' := (localUltraMk_mem_iff _ _ _ _).2 (Filter.Eventually.of_forall fun i => (hA i).one_mem)
  have hAi : ∀ x ∈ A', M.inv x ∈ A' :=
    (localUltra_inv_closed_iff U G L _).2 (Filter.Eventually.of_forall fun i => (hA i).inv_mem)
  have hA2 : M.AllProductsDefined A' 2 := (localUltra_allProductsDefined_iff U G L _ 2).2
    (Filter.Eventually.of_forall fun i => (hA i).allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200))
  have hbin : ∀ x ∈ A', ∀ y ∈ A', M.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hA2 [x,y] (by simp) (by aesop)
    exact ⟨z,(LocalGroupAlgebra.Product.pair_iff M x y z).1 hz⟩
  obtain ⟨K,R₁,hK,hR₁,hstrong⟩ := large_strong_local_groups_from_local_lie_model X hQ U G L
    (localUltraAlgebra_divisionClosed (U : Filter ι) G L hd) (localUltraAlgebra_reversible (U : Filter ι) G L hr)
    π A hA1 hAi hbin C hC hAC W hW hsmall hsandwich
  obtain ⟨R₂,hR₂,hwords⟩ := exists_local_lie_model_word_escape_radius X U G L
    (fun i => (A i : Set (G i))) hA1 hbin π W hW (fun _ hx => hsmall hx) m hε
  refine ⟨K,min R₁ R₂,hK,lt_min hR₁ hR₂,?_⟩
  intro r hrpos hrR
  obtain ⟨B,J,hJ,hBin,hBout,hBs⟩ := hstrong r hrpos (hrR.trans_le (min_le_left _ _))
  have hw := hwords r hrpos (hrR.trans_le (min_le_right _ _)) (fun i => (B i : Set (G i)))
    (by rintro _ ⟨x,hx,rfl⟩; exact Set.image_mono Metric.ball_subset_closedBall (hBout hx))
  obtain ⟨B',he,heSet,hgood⟩ := local_finite_word_window_normalization U G L A B (fun i => (hA i).one_mem) hK hε
    (by
      filter_upwards [hBs,hw] with i hi hwi
      exact ⟨hi.2.2.approximate,hwi.1,hwi.2⟩)
  refine ⟨B',J,hJ,?_,?_,hgood,?_,?_⟩
  · rw [heSet]
    exact hBin
  · rw [heSet]
    exact hBout
  · filter_upwards [he,hBs] with i hei hi
    rw [hei]
    exact hi.2.2
  · filter_upwards [he,hBs] with i hei hi
    rw [hei]
    exact hi.2.1
end DirectedCycles
