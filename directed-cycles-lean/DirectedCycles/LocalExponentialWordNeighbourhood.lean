module

public import DirectedCycles.LocalExponentialWordControl
public import DirectedCycles.LocalExponentialBallTopology
public import DirectedCycles.LocalToLocalModelWordDomains

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalExponentialData
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G} (D : LocalExponentialData (E := E) L)

include D in
/-- Every identity neighbourhood contains all bounded-length products of an
actual open symmetric smaller neighbourhood. All bracketings are constructed
using local associativity and quantitative exponential word control. -/
theorem exists_open_word_neighbourhood (U : Set G) (hU : U ∈ 𝓝 L.one) (M : ℕ) :
    ∃ W : Set G, IsOpen W ∧ L.one ∈ W ∧ (∀ x ∈ W, L.inv x ∈ W) ∧ W ⊆ U ∧
      L.AllProductsDefined W M ∧ ∀ n ≤ M, L.wordPower W n ⊆ U := by
  have hpre : D.chart ⁻¹' U ∈ 𝓝 (0 : E) := by
    apply (D.chart.continuousAt D.zero_mem).preimage_mem_nhds
    simpa only [D.zero] using hU
  obtain ⟨Rw,hRw,hw⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨Rp,hRp,hprod⟩ := D.product_norm_bound (by norm_num : (0 : ℝ)<1)
  obtain ⟨R,hR,hword⟩ := D.word_control M
  let a : ℝ := min Rp Rw/4
  have ha : 0 < a := div_pos (lt_min hRp hRw) (by norm_num)
  have haRp : a < Rp := by dsimp only [a]; have := min_le_left Rp Rw; linarith
  have haRw : a < Rw := by dsimp only [a]; have := min_le_right Rp Rw; linarith
  let b : ℝ := min R (min a D.radius)/(4*((M : ℝ)+1))
  have hden : 0 < 4*((M : ℝ)+1) := by positivity
  have hb : 0 < b := div_pos (lt_min hR (lt_min ha D.radius_pos)) hden
  have hscale : 4*((M : ℝ)+1)*b = min R (min a D.radius) := by
    dsimp only [b]
    field_simp
  have hscaleR : 4*((M : ℝ)+1)*b ≤ R := by rw [hscale]; exact min_le_left _ _
  have hscaleA : 4*((M : ℝ)+1)*b ≤ a := by rw [hscale]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hscaleD : 4*((M : ℝ)+1)*b ≤ D.radius := by rw [hscale]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hbA : b ≤ a := by nlinarith
  have hbD : 2*b < D.radius := by nlinarith
  have hbR : 2*(M+1 : ℝ)*b < R := by nlinarith
  have hMbA : 2*(M : ℝ)*b ≤ a := by nlinarith
  let A : Set G := D.chart '' Metric.closedBall (0 : E) a
  let W : Set G := D.chart '' Metric.ball (0 : E) b
  have hA1 : L.one ∈ A := ⟨0,by simpa only [Metric.mem_closedBall,dist_self] using ha.le,D.zero⟩
  have hAU : A ⊆ U := by
    rintro x ⟨v,hv,rfl⟩
    exact hw ((Metric.closedBall_subset_ball haRw) hv)
  have hWA : W ⊆ A := Set.image_mono ((Metric.ball_subset_closedBall).trans (Metric.closedBall_subset_closedBall hbA))
  have hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y := by
    rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩
    have hvn : ‖v‖ < Rp := (by simpa only [Metric.mem_closedBall,dist_zero_right] using hv : ‖v‖ ≤ a).trans_lt haRp
    have hwn : ‖w‖ < Rp := (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw : ‖w‖ ≤ a).trans_lt haRp
    obtain ⟨z,_,hz⟩ := hprod v w hvn hwn
    exact ⟨D.chart z,hz⟩
  have hwords : ∀ l : List G, l.length ≤ M → (∀ x ∈ l, x ∈ W) →
      ∀ z : G, L.Product l z → z ∈ A := by
    intro l hl hm z hz
    obtain ⟨v,hv,he⟩ := hword b hb.le hbR l hl
      (fun x hx => Set.image_mono Metric.ball_subset_closedBall (hm x hx)) z hz
    refine ⟨v,?_,he⟩
    simp only [Metric.mem_closedBall,dist_zero_right]
    have hlr : (l.length : ℝ) ≤ M := by exact_mod_cast hl
    exact hv.trans ((mul_le_mul_of_nonneg_right (by linarith : 2*(l.length : ℝ) ≤ 2*M) hb.le).trans hMbA)
  obtain ⟨hWdom,hWp⟩ := L.allProductsDefined_of_local_model_words L A W hA1 hWA hdom
    (LocalGroupHom.id L) A (fun _ h => h) M (by
      intro l hl hm z hz
      apply hwords l hl hm z
      simpa only [LocalGroupHom.id,List.map_id_fun,id_eq] using hz)
  refine ⟨W,D.ball_open (by linarith),⟨0,by simpa only [Metric.mem_ball,dist_self] using hb,D.zero⟩,
    ?_,hWA.trans hAU,hWdom,fun n hn => (hWp n hn).trans hAU⟩
  rintro _ ⟨v,hv,rfl⟩
  have hvn : ‖v‖ < b := by simpa only [Metric.mem_ball,dist_zero_right] using hv
  exact ⟨-v,by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hvn,D.inv_chart (by linarith)⟩
end DirectedCycles.LocalExponentialData
