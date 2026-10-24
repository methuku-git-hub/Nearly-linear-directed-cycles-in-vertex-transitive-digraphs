import DirectedCycles.LocalExponentialProductBounds
import DirectedCycles.LocalExponentialWordBoundRel
import DirectedCycles.LieExponentialWordControl

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {G E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] {L : LocalGroupAlgebra G} (D : LocalExponentialData (E := E) L)

/-- One radius controls every actual bounded-length word in a local
exponential ball, with a uniform factor two in its coordinate norm. -/
theorem word_control (M : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 ≤ r → 2*(M+1 : ℝ)*r < R →
      ∀ l : List G, l.length ≤ M →
        (∀ x ∈ l, x ∈ D.chart '' Metric.closedBall (0 : E) r) →
        ∀ x : G, L.Product l x → ∃ v : E, ‖v‖ ≤ 2*(l.length : ℝ)*r ∧ D.chart v = x := by
  obtain ⟨q,hq,hqM⟩ := exists_power_slack M
  obtain ⟨R,hR,hprod⟩ := D.product_norm_bound (sub_pos.mpr hq)
  refine ⟨R,hR,?_⟩
  intro r hr hsize l hl hm x hx
  have hrR : r < R := by
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  have hqbound : q^M*(M : ℝ)*r < R := by
    calc
      q^M*(M : ℝ)*r ≤ 2*(M : ℝ)*r := by gcongr
      _ ≤ 2*(M+1 : ℝ)*r := by gcongr; linarith
      _ < R := hsize
  obtain ⟨v,hv,he⟩ := local_exponential_word_bound_rel L D.chart D.zero hq.le hr hrR M hqbound
    (by simpa only [add_sub_cancel] using hprod) l hl hm x hx
  refine ⟨v,hv.trans ?_,he⟩
  have hpow : q^l.length ≤ q^M := pow_le_pow_right₀ hq.le hl
  gcongr
  exact hpow.trans hqM.le
end LocalExponentialData
end DirectedCycles
