module

public import DirectedCycles.LocalExponentialConjugationError
public import DirectedCycles.LocalExponentialPowerTest
public import DirectedCycles.LocalExponentialWordControl

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G}

/-- Strong trapping tests stated using actual local powers and conjugate
words in an exponential chart. -/
structure LocalLieStrongTrappingWindows (D : LocalExponentialData (E := E) L) (T : ℕ) (r : ℝ) : Prop where
  conjugateWords : L.wordPower (L.conjugates
      (D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*(r/(10*(T : ℝ)))))
      (L.wordPower (D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)) 4)) T
    ⊆ D.chart '' Metric.ball (0 : E) r
  firstPowerTest : ∀ x : G, (∀ n : ℕ, 1 ≤ n → n ≤ 1000 →
      L.PowerIn (L.wordPower (D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)) 100) x n) →
    x ∈ D.chart '' Metric.ball (0 : E) r
  secondPowerTest : ∀ x : G, (∀ n : ℕ, 1 ≤ n → n ≤ 1000*T →
      L.PowerIn (D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)) x n) →
    x ∈ D.chart '' Metric.ball (0 : E) (r/(10*(T : ℝ)))

/-- A smooth local exponential chart has arbitrarily small strong trapping
windows. The radius depends on the finite trapping length; exact bounded
powers and the proved coordinate error suffice without globalizing the group. -/
theorem exists_local_lie_strong_trapping_windows (D : LocalExponentialData (E := E) L)
    (T : ℕ) (hT : 1 ≤ T) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R → LocalLieStrongTrappingWindows D T r := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < T := by linarith
  let ε : ℝ := 1/(1000*(T : ℝ))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := by dsimp only [ε]; rw [div_le_iff₀ (by positivity)]; linarith
  have hTε : (T : ℝ)*ε = 1/1000 := by dsimp only [ε]; field_simp
  obtain ⟨Rw,hRw,hw⟩ := D.word_control (T+100)
  obtain ⟨Rc,hRc,hc⟩ := D.conjugate_word_error hε hε1
  let C : ℝ := 1000000*((T : ℝ)+101)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨min Rw (min Rc D.radius)/C,div_pos (lt_min hRw (lt_min hRc D.radius_pos)) hC,?_⟩
  intro r hr hrr
  have hCr : C*r < min Rw (min Rc D.radius) := by nlinarith [(lt_div_iff₀ hC).1 hrr]
  have hCw : C*r < Rw := hCr.trans_le (min_le_left _ _)
  have hCc : C*r < Rc := hCr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hCd : C*r < D.radius := hCr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hword : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ (1001/1000 : ℝ)*r → ∀ l : List G,
      l.length ≤ T+100 → (∀ x ∈ l, x ∈ D.chart '' Metric.closedBall (0 : E) ρ) →
      ∀ z : G, L.Product l z → ∃ v : E, ‖v‖ ≤ 2*(l.length : ℝ)*ρ ∧ D.chart v = z := by
    intro ρ hρ hρr l hl hm z hz
    apply hw ρ hρ _ l hl hm z hz
    push_cast
    have hmult := mul_le_mul_of_nonneg_left hρr (show 0 ≤ 2*((T : ℝ)+100+1) by positivity)
    dsimp only [C] at hCw
    nlinarith
  have hwordSet : ∀ n : ℕ, n ≤ T+100 →
      L.wordPower (D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)) n ⊆
        D.chart '' Metric.closedBall (0 : E) (2*(n : ℝ)*(1001/1000 : ℝ)*r) := by
    intro n hn z hz
    obtain ⟨l,hlen,hl,hp⟩ := hz
    obtain ⟨v,hv,he⟩ := hword _ (by positivity) le_rfl l (hlen ▸ hn) hl z hp
    refine ⟨v,?_,he⟩
    simpa only [Metric.mem_closedBall,dist_zero_right,hlen,mul_assoc] using hv
  have hconj : L.conjugates
      (D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*(r/(10*(T : ℝ)))))
      (L.wordPower (D.chart '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)) 4) ⊆
      D.chart '' Metric.closedBall (0 : E) (r/(4*(T : ℝ))) := by
    rintro z ⟨y,hy,x,hx,hp⟩
    obtain ⟨v,hv,hev⟩ := hwordSet 4 (by omega) hx
    obtain ⟨w,hw,hew⟩ := hy
    have hvn : ‖v‖ ≤ 8*(1001/1000 : ℝ)*r := by
      simp only [Metric.mem_closedBall,dist_zero_right,Nat.cast_ofNat] at hv
      linarith
    have hwn : ‖w‖ ≤ (1001/1000 : ℝ)*(r/(10*(T : ℝ))) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    have hwT : (T : ℝ)*‖w‖ ≤ (1001/10000 : ℝ)*r := by
      have hh := mul_le_mul_of_nonneg_left hwn hTp.le
      have he : (T : ℝ)*((1001/1000 : ℝ)*(r/(10*(T : ℝ)))) = (1001/10000 : ℝ)*r := by field_simp; ring
      exact he ▸ hh
    have hwr : ‖w‖ ≤ (1001/1000 : ℝ)*r := by nlinarith [norm_nonneg w]
    obtain ⟨u,hu,heu⟩ := hc v w (by dsimp only [C] at hCc; nlinarith)
      (by dsimp only [C] at hCc; nlinarith) z (by simpa only [hev,hew] using hp)
    have huT : (T : ℝ)*‖u‖ ≤ (T : ℝ)*‖w‖+(1/1000 : ℝ)*(4*‖v‖+3*‖w‖) := by
      have hh := mul_le_mul_of_nonneg_left hu hTp.le
      simpa only [mul_add,← mul_assoc,hTε] using hh
    have hub : ‖u‖ ≤ r/(4*(T : ℝ)) := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith
    exact ⟨u,by simpa only [Metric.mem_closedBall,dist_zero_right] using hub,heu⟩
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain ⟨l,hlen,hl,hp⟩ := hz
    have hρ : 0 ≤ r/(4*(T : ℝ)) := by positivity
    have hρr : r/(4*(T : ℝ)) ≤ (1001/1000 : ℝ)*r := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    obtain ⟨v,hv,he⟩ := hword _ hρ hρr l (by omega) (fun x hx => hconj (hl x hx)) z hp
    have hhalf : 2*(T : ℝ)*(r/(4*(T : ℝ))) = r/2 := by field_simp; ring
    have hvsmall : ‖v‖ < r := by rw [hlen,hhalf] at hv; linarith
    exact ⟨v,by simpa only [Metric.mem_ball,dist_zero_right] using hvsmall,he⟩
  · intro x hx
    have hs : (1000 : ℝ)*(2*(100 : ℝ)*(1001/1000 : ℝ)*r) < D.radius := by
      dsimp only [C] at hCd
      nlinarith
    obtain ⟨v,he,hv⟩ := D.power_test (by positivity) (by norm_num : 1 ≤ 1000) hs
      (hwordSet 100 (by omega)) x (hx 1 (by omega) (by omega)) (hx 1000 (by omega) le_rfl)
    have hvsmall : ‖v‖ < r := by norm_num at hv; linarith
    exact ⟨v,by simpa only [Metric.mem_ball,dist_zero_right] using hvsmall,he⟩
  · intro x hx
    have hN : 1 ≤ 1000*T := by omega
    have hs : ((1000*T : ℕ) : ℝ)*((1001/1000 : ℝ)*r) < D.radius := by
      push_cast
      dsimp only [C] at hCd
      nlinarith
    obtain ⟨v,he,hv⟩ := D.power_test (by positivity) hN hs (Set.Subset.refl _) x
      (hx 1 (by omega) hN) (hx (1000*T) hN le_rfl)
    have hvsmall : ‖v‖ < r/(10*(T : ℝ)) := by
      apply (lt_div_iff₀ (by positivity)).2
      push_cast at hv
      nlinarith
    exact ⟨v,by simpa only [Metric.mem_ball,dist_zero_right] using hvsmall,he⟩
end DirectedCycles
