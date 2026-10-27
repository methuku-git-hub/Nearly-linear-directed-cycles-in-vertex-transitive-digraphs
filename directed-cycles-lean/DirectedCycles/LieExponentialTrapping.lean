module

public import DirectedCycles.LieExponentialWordControl
public import DirectedCycles.LieExponentialConjugationBound
public import DirectedCycles.LieExponentialFinitePowerControl
public import DirectedCycles.LieExponentialSymmetry
public import DirectedCycles.LocalGlobalWordPowers
public import DirectedCycles.LocalConjugates

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

/-- Quantitative exponential windows give all three strong-group trapping
conditions in the genuine Lie target. The source transfer is a separate step. -/
theorem lie_exponential_trapping_at_scale (L : ℕ) (hL : 1 ≤ L) {r R : ℝ} (hr : 0 < r)
    (hR : 400*(1001/1000 : ℝ)*r < R)
    (hinj : Set.InjOn (lieExponential (G := G) (E := E)) (Metric.ball 0 R))
    (hword : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ (1001/1000 : ℝ)*r → ∀ l : List G,
      l.length ≤ L+100 →
      (∀ x ∈ l, x ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ) →
      ∃ v : E, ‖v‖ ≤ 2*(l.length : ℝ)*ρ ∧ lieExponential (G := G) v = l.prod)
    (hconj : ∀ x y : E, ‖x‖ ≤ 8*(1001/1000 : ℝ)*r → ‖y‖ ≤ (1001/1000 : ℝ)*r →
      ∃ z : E, ‖z‖ ≤ 4*‖y‖ ∧ lieExponential (G := G) z =
        lieExponential x*lieExponential y*(lieExponential x)⁻¹) :
    let exp : E → G := lieExponential (G := G)
    let A := exp '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)
    let s := r/(10*(L : ℝ))
    let S := exp '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*s)
    (LocalGroupAlgebra.ofGroup G).wordPower
      ((LocalGroupAlgebra.ofGroup G).conjugates S ((LocalGroupAlgebra.ofGroup G).wordPower A 4)) L
        ⊆ exp '' Metric.ball (0 : E) r ∧
    (∀ x : G, (∀ n : ℕ, 1 ≤ n → n ≤ 1000 →
      x^n ∈ (LocalGroupAlgebra.ofGroup G).wordPower A 100) → x ∈ exp '' Metric.ball (0 : E) r) ∧
    (∀ x : G, (∀ n : ℕ, 1 ≤ n → n ≤ 1000*L → x^n ∈ A) →
      x ∈ exp '' Metric.ball (0 : E) s) := by
  dsimp only
  let exp : E → G := lieExponential (G := G)
  let a : ℝ := 1001/1000
  let s := r/(10*(L : ℝ))
  let A := exp '' Metric.closedBall (0 : E) (a*r)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLp : (0 : ℝ) < L := by linarith
  have hs : 0 < s := div_pos hr (by positivity)
  have hscale : 10*(L : ℝ)*s = r := by dsimp only [s]; field_simp
  have hs4 : 4*s ≤ r := by nlinarith
  have ha : 0 < a := by norm_num [a]
  have hwords : ∀ {n : ℕ}, n ≤ L+100 → ∀ x ∈ (LocalGroupAlgebra.ofGroup G).wordPower A n,
      ∃ v : E, ‖v‖ ≤ 2*(n : ℝ)*(a*r) ∧ exp v = x := by
    intro n hn x hx
    obtain ⟨l,hlen,hl,hp⟩ := hx
    obtain ⟨v,hv,he⟩ := hword (a*r) (by positivity) le_rfl l (hlen ▸ hn) hl
    exact ⟨v,by simpa only [hlen] using hv,he.trans ((LocalGroupAlgebra.ofGroup_product_iff G l x).1 hp).symm⟩
  have hzero : ∀ ρ : ℝ, 0 ≤ ρ → (1 : G) ∈ exp '' Metric.closedBall (0 : E) ρ := by
    intro ρ hρ
    exact ⟨0,by simpa only [Metric.mem_closedBall,dist_self] using hρ,lieExponential_zero⟩
  refine ⟨?_,?_,?_⟩
  · intro x hx
    obtain ⟨l,hlen,hl,hp⟩ := hx
    have hletters : ∀ z ∈ l, z ∈ exp '' Metric.closedBall (0 : E) (4*a*s) := by
      intro z hz
      obtain ⟨b,hb,y,hy,hyz⟩ := hl z hz
      obtain ⟨v,hv,hev⟩ := hwords (by omega : 4 ≤ L+100) y hy
      obtain ⟨w,hw,hew⟩ := hb
      have hwn : ‖w‖ ≤ a*s := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
      obtain ⟨t,ht,het⟩ := hconj (-v) w (by rw [norm_neg]; dsimp only [a] at hv; norm_num only [Nat.cast_ofNat] at hv; linarith)
        (hwn.trans (by nlinarith))
      refine ⟨t,?_,?_⟩
      · simp only [Metric.mem_closedBall,dist_zero_right]
        nlinarith
      · have hzprod := (LocalGroupAlgebra.ofGroup_product_iff G _ z).1 hyz
        change z = [y⁻¹,b,y].prod at hzprod
        calc
          lieExponential t = lieExponential (-v)*lieExponential w*(lieExponential (-v))⁻¹ := het
          _ = y⁻¹*b*y := by rw [lieExponential_neg,show lieExponential v = y from hev,show lieExponential w = b from hew,inv_inv]
          _ = z := by simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hzprod.symm
    obtain ⟨v,hv,hev⟩ := hword (4*a*s) (by positivity) (by nlinarith) l (by omega) hletters
    refine ⟨v,?_,hev.trans ((LocalGroupAlgebra.ofGroup_product_iff G l x).1 hp).symm⟩
    simp only [Metric.mem_ball,dist_zero_right]
    rw [hlen] at hv
    dsimp only [a] at hv
    nlinarith
  · intro x hx
    have hp : ∀ n ≤ 1000, x^n ∈ exp '' Metric.closedBall (0 : E) (200*a*r) := by
      intro n hn
      by_cases hn0 : n = 0
      · simpa only [hn0,pow_zero] using hzero (200*a*r) (by positivity)
      · obtain ⟨v,hv,he⟩ := hwords (by omega : 100 ≤ L+100) (x^n) (hx n (by omega) hn)
        refine ⟨v,?_,he⟩
        simp only [Metric.mem_closedBall,dist_zero_right]
        norm_num only [Nat.cast_ofNat] at hv
        dsimp only [a]
        nlinarith
    apply lie_exponential_inner_of_finite_powers (by positivity : 0 ≤ 200*a*r)
      (by dsimp only [a]; linarith) hinj (by simpa only [pow_one] using hp 1 (by omega)) 1000 (by omega) _ hp
    dsimp only [a]
    norm_num
    linarith
  · intro x hx
    have hp : ∀ n ≤ 1000*L, x^n ∈ A := by
      intro n hn
      by_cases hn0 : n = 0
      · simpa only [hn0,pow_zero] using hzero (a*r) (by positivity)
      · exact hx n (by omega) hn
    apply lie_exponential_inner_of_finite_powers (by positivity : 0 ≤ a*r)
      (by dsimp only [a]; nlinarith) hinj (by simpa only [pow_one] using hp 1 (by omega)) (1000*L) (by omega) _ hp
    push_cast
    dsimp only [a]
    nlinarith
end DirectedCycles
