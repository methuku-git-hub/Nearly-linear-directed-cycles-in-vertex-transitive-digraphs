import DirectedCycles.LieExponentialTrapping
import DirectedCycles.LieExponentialRadialControl

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

/-- The exact target inclusions used to transfer strong trapping to finite
local source components. Both inner sets are open exponential balls. -/
structure LieStrongTrappingWindows (G E : Type*) [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G] (L : ℕ) (r : ℝ) : Prop where
  conjugateWords :
    (LocalGroupAlgebra.ofGroup G).wordPower
      ((LocalGroupAlgebra.ofGroup G).conjugates
        ((lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*(r/(10*(L : ℝ)))))
        ((LocalGroupAlgebra.ofGroup G).wordPower
          ((lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)) 4)) L
      ⊆ (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) r
  firstPowerTest : ∀ x : G, (∀ n : ℕ, 1 ≤ n → n ≤ 1000 →
      x^n ∈ (LocalGroupAlgebra.ofGroup G).wordPower
        ((lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)) 100) →
      x ∈ (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) r
  secondPowerTest : ∀ x : G, (∀ n : ℕ, 1 ≤ n → n ≤ 1000*L →
      x^n ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r)) →
      x ∈ (lieExponential (G := G) (E := E)) '' Metric.ball (0 : E) (r/(10*(L : ℝ)))

/-- Every genuine smooth Lie group has arbitrarily small exponential
windows satisfying the strong-group trapping tests with the stated constants. -/
theorem exists_lie_strong_trapping_windows (L : ℕ) (hL : 1 ≤ L) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → LieStrongTrappingWindows G E L r := by
  obtain ⟨Rw,hRw,hw⟩ := lie_exponential_word_control (G := G) (E := E) (L+100)
  obtain ⟨Rc,hRc,hc⟩ := lie_exponential_conjugation_norm_bound (G := G) (E := E)
  obtain ⟨Ri,hRi,hinj,_⟩ := lie_exponential_radial_control (G := G) (E := E)
  let b := min Rw (min Rc Ri)
  let C : ℝ := 1000*((L : ℝ)+101)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hb : 0 < b := lt_min hRw (lt_min hRc hRi)
  refine ⟨b/C,div_pos hb hC,?_⟩
  intro r hr hrr
  have hCr : C*r < b := by nlinarith [(lt_div_iff₀ hC).1 hrr]
  have hCw : C*r < Rw := hCr.trans_le (min_le_left _ _)
  have hCc : C*r < Rc := hCr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hCi : C*r < Ri := hCr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hLr : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hR : 400*(1001/1000 : ℝ)*r < Ri := by dsimp only [C] at hCi; nlinarith
  have hword : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ (1001/1000 : ℝ)*r → ∀ l : List G,
      l.length ≤ L+100 →
      (∀ x ∈ l, x ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) ρ) →
      ∃ v : E, ‖v‖ ≤ 2*(l.length : ℝ)*ρ ∧ lieExponential (G := G) v = l.prod := by
    intro ρ hρ hρr l hl hm
    apply hw ρ hρ _ l hl hm
    push_cast
    have hmult := mul_le_mul_of_nonneg_left hρr (show 0 ≤ 2*((L : ℝ)+100+1) by positivity)
    dsimp only [C] at hCw
    nlinarith
  have hconj : ∀ x y : E, ‖x‖ ≤ 8*(1001/1000 : ℝ)*r → ‖y‖ ≤ (1001/1000 : ℝ)*r →
      ∃ z : E, ‖z‖ ≤ 4*‖y‖ ∧ lieExponential (G := G) z =
        lieExponential x*lieExponential y*(lieExponential x)⁻¹ := by
    intro x y hx hy
    apply hc x y
    · dsimp only [C] at hCc; nlinarith
    · dsimp only [C] at hCc; nlinarith
  obtain ⟨h₁,h₂,h₃⟩ := lie_exponential_trapping_at_scale L hL hr hR hinj hword hconj
  exact ⟨h₁,h₂,h₃⟩
end DirectedCycles
