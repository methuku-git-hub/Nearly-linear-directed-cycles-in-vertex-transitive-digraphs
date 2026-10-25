module

public import DirectedCycles.LocalCoordinateApproximateCover
public import DirectedCycles.LieExponentialWordControl
public import DirectedCycles.LieExponentialDifferenceBound
public import DirectedCycles.UniformScaledBallCover
public import DirectedCycles.LocalWordPowerMaps

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G H E : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] [LieGroup 𝓘(ℝ,E) ∞ H]

/-- A fixed coordinate cover supplies one approximate-group constant for
all sufficiently small source sets sandwiched by concentric exponential
balls. The covering centres are actual elements of the source square. -/
theorem exists_uniform_lie_sandwich_approximate :
    ∃ K : ℕ, ∃ r₀ : ℝ, 1 ≤ K ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ L : LocalGroupAlgebra G, L.DivisionClosed → L.Reversible →
      ∀ π : LocalGroupHom L (LocalGroupAlgebra.ofGroup H), ∀ A : Set G,
      L.one ∈ A → (∀ x ∈ A, L.inv x ∈ A) → L.AllProductsDefined A 200 →
      π.toFun '' A ⊆ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r) →
      (∀ x ∈ L.wordPower A 4, π.toFun x ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r → x ∈ A) →
      IsLocalApproximateSet L K A := by
  classical
  obtain ⟨F,hF⟩ := uniform_scaled_ball_cover (E := E) 5 (show (0 : ℝ) < 1/16 by norm_num)
  obtain ⟨Rw,hRw,hw⟩ := lie_exponential_word_control (G := H) (E := E) 2
  obtain ⟨Rd,hRd,hdiff⟩ := lie_exponential_difference_bound (G := H) (E := E)
    (show (0 : ℝ) < 1/100 by norm_num)
  refine ⟨2*(F.card+1),min Rw Rd/10,by omega,div_pos (lt_min hRw hRd) (by norm_num),?_⟩
  intro r hr hrr L hd hl π A hA1 hAi hdom hAout hAin
  have hscale : 10*r < min Rw Rd := by linarith [(lt_div_iff₀ (show (0 : ℝ) < 10 by norm_num)).1 hrr]
  have hrw : 10*r < Rw := hscale.trans_le (min_le_left _ _)
  have hrd : 10*r < Rd := hscale.trans_le (min_le_right _ _)
  have hcoords : ∀ x ∈ L.wordPower A 2, ∃ v : E, ‖v‖ ≤ 5*r ∧ lieExponential (G := H) v = π.toFun x := by
    intro x hx
    obtain ⟨l,hlen,hl,hp⟩ := hx
    obtain ⟨v,hv,he⟩ := hw ((1001/1000 : ℝ)*r) (by positivity)
      (by norm_num; linarith) (l.map π.toFun) (by simp only [List.length_map,hlen,le_refl]) (by
        intro y hy
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
        exact hAout ⟨a,hl a ha,rfl⟩)
    refine ⟨v,?_,?_⟩
    · simp only [List.length_map,hlen,Nat.cast_ofNat] at hv
      nlinarith
    · exact he.trans ((LocalGroupAlgebra.ofGroup_product_iff H _ _).1 (hp.map π)).symm
  have hex : ∀ x : G, ∃ v : E, x ∈ L.wordPower A 2 →
      ‖v‖ ≤ 5*r ∧ lieExponential (G := H) v = π.toFun x := by
    intro x
    by_cases hx : x ∈ L.wordPower A 2
    · obtain ⟨v,hv⟩ := hcoords x hx
      exact ⟨v,fun _ => hv⟩
    · exact ⟨0,fun h => (hx h).elim⟩
  choose v hv using hex
  apply local_approximate_of_coordinate_cover L hd hl A hA1 hAi hdom v F (r := r)
  · intro x hx
    obtain ⟨c,hc,he⟩ := hF r hr (v x) (hv x hx).1
    exact ⟨c,hc,by linarith⟩
  · intro x hx y hy hxy d hmul
    have hvx := hv x hx
    have hvy := hv y hy
    obtain ⟨z,hz,hez⟩ := hdiff (v x) (v y) (by linarith) (by linarith)
    have hzsmall : ‖z‖ < r := by rw [norm_sub_rev] at hxy; nlinarith
    have hd4 : d ∈ L.wordPower A 4 := by
      rw [show 4 = 2+2 from rfl,L.wordPower_add hdom (by norm_num)]
      exact ⟨L.inv x,L.inv_mem_wordPower hl hAi hx,y,hy,hmul⟩
    apply hAin d hd4
    refine ⟨z,by simpa only [Metric.mem_ball,dist_zero_right] using hzsmall,?_⟩
    have hπ := π.map_mul hmul
    rw [π.map_inv] at hπ
    change (π.toFun x)⁻¹*π.toFun y = π.toFun d at hπ
    have hez' : lieExponential (G := H) z = (π.toFun x)⁻¹*π.toFun y := by
      simpa only [hvx.2,hvy.2] using hez
    exact hez'.trans hπ
end DirectedCycles
