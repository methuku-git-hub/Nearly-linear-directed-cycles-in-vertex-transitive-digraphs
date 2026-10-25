module

public import DirectedCycles.LieExponentialProductCoordinates
public import DirectedCycles.LocalExponentialWordBound

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles

/-- Continuity of a fixed power at one supplies the quantitative slack for
all word lengths up to a prescribed finite bound. -/
theorem exists_power_slack (M : ℕ) : ∃ q : ℝ, 1 < q ∧ q^M < 2 := by
  have he : ∀ᶠ q : ℝ in 𝓝 1, q^M < 2 :=
    (continuousAt_pow (1 : ℝ) M).preimage_mem_nhds (Iio_mem_nhds (by simp))
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1+r/2,by linarith,hrb ?_⟩
  simp only [Metric.mem_ball,Real.dist_eq,add_sub_cancel_left]
  rw [abs_of_pos (by positivity : 0 < r/2)]
  linarith

variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]

/-- A single radius controls every word of at most M exponential letters.
The factor two is independent of the word length; the radius depends on M. -/
theorem lie_exponential_word_control (M : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 ≤ r → 2*(M+1 : ℝ)*r < R →
      ∀ l : List G, l.length ≤ M →
        (∀ x ∈ l, x ∈ (lieExponential (G := G) (E := E)) '' Metric.closedBall (0 : E) r) →
        ∃ v : E, ‖v‖ ≤ 2*(l.length : ℝ)*r ∧ lieExponential (G := G) v = l.prod := by
  obtain ⟨q,hq,hqM⟩ := exists_power_slack M
  obtain ⟨R,hR,hprod⟩ := lie_exponential_product_norm_bound (G := G) (E := E)
    (sub_pos.mpr hq)
  refine ⟨R,hR,?_⟩
  intro r hr hsize l hl hm
  have hrR : r < R := by
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  have hqbound : q^M*(M : ℝ)*r < R := by
    calc
      q^M*(M : ℝ)*r ≤ 2*(M : ℝ)*r := by gcongr
      _ ≤ 2*(M+1 : ℝ)*r := by gcongr; linarith
      _ < R := hsize
  obtain ⟨v,hv,he⟩ := local_exponential_word_bound (lieExponential (G := G))
    lieExponential_zero hq.le hr hrR M hqbound
    (by simpa only [add_sub_cancel] using hprod) l hl hm
  refine ⟨v,hv.trans ?_,he⟩
  have hpow : q^l.length ≤ q^M := pow_le_pow_right₀ hq.le hl
  gcongr
  exact hpow.trans hqM.le
end DirectedCycles
