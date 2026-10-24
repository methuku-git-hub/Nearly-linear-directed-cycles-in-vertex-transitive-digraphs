import DirectedCycles.LocalToLocalModelWordDomains
import DirectedCycles.LocalExponentialWordControl

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G H E : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    {M : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) M)

/-- A Lie model's small inverse-image neighbourhood supplies every bounded
source word domain after shrinking its exponential radius. Only binary
products in the original source window are assumed. -/
theorem exists_local_lie_model_word_domain_radius (L : LocalGroupAlgebra G)
    (A : Set G) (hA1 : L.one ∈ A) (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (π : LocalGroupHom L M) (W : Set H) (hW : W ∈ 𝓝 M.one)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ A) (N : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R → ∀ B : Set G,
      π.toFun '' B ⊆ D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r) →
      B ⊆ A ∧ L.AllProductsDefined B N ∧ ∀ n ≤ N, L.wordPower B n ⊆ A := by
  have hc := D.chart.continuousAt D.zero_mem
  have hpre : D.chart ⁻¹' W ∈ 𝓝 (0 : E) := by
    apply hc.preimage_mem_nhds
    simpa only [D.zero] using hW
  obtain ⟨ρ,hρ,hρW⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨Rw,hRw,hw⟩ := D.word_control N
  let C : ℝ := 10*((N : ℝ)+1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨min Rw ρ/C,div_pos (lt_min hRw hρ) hC,?_⟩
  intro r hr hrR B hB
  have hCr : C*r < min Rw ρ := by nlinarith [(lt_div_iff₀ hC).1 hrR]
  have hRwr : C*r < Rw := hCr.trans_le (min_le_left _ _)
  have hρr : C*r < ρ := hCr.trans_le (min_le_right _ _)
  have hNnon : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hBA : B ⊆ A := by
    intro x hx
    obtain ⟨v,hv,he⟩ := hB ⟨x,hx,rfl⟩
    have hvn : ‖v‖ ≤ (1001/1000 : ℝ)*r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
    apply hsmall x
    rw [← he]
    apply hρW
    simp only [Metric.mem_ball,dist_zero_right]
    dsimp only [C] at hρr
    nlinarith
  refine ⟨hBA,L.allProductsDefined_of_local_model_words M A B hA1 hBA hdom π W hsmall N ?_⟩
  intro l hlen hl z hz
  obtain ⟨v,hv,he⟩ := hw ((1001/1000 : ℝ)*r) (by positivity)
    (by dsimp only [C] at hRwr; nlinarith) (l.map π.toFun)
    (by simpa only [List.length_map] using hlen) (by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact hB ⟨y,hl y hy,rfl⟩) z hz
  rw [← he]
  apply hρW
  simp only [Metric.mem_ball,dist_zero_right]
  have hlenr : (l.length : ℝ) ≤ N := by exact_mod_cast hlen
  simp only [List.length_map] at hv
  dsimp only [C] at hρr
  nlinarith
end DirectedCycles
