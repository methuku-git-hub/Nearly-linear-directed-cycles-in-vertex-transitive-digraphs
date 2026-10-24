import DirectedCycles.GleasonLieAlgebraTopology
import DirectedCycles.GleasonExponentialInjection

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace GleasonLieAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Evaluation at one on the constructed finite-dimensional curve space. -/
def exp (x : GleasonLieAlgebra D) : G := (toOneParameter D x).eval 1

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
@[simp] theorem exp_zero : exp D 0 = 1 := rfl

theorem exp_smul (c : ℝ) (x : GleasonLieAlgebra D) :
    exp D (c • x) = (toOneParameter D x).eval c := by
  change ((OneParameter.scale c (toOneParameter D x)).eval 1) = _
  rw [OneParameter.scale_eval,mul_one]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
theorem continuous_exp : Continuous (exp D) :=
  (continuous_eval_const (Multiplicative.ofAdd (1 : ℝ))).comp (toOneParameter D).continuous

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- The evaluation map has an injective neighbourhood in the actual
finite-dimensional vector space, with its original compact-open topology. -/
theorem exp_locally_injective : ∃ U : Set (GleasonLieAlgebra D), U ∈ 𝓝 0 ∧ Set.InjOn (exp D) U :=
  D.exponential_locally_injective

/-- The actual vector sum has a quadratic error from multiplication after
evaluation, at the radius constructed by the power estimates. -/
theorem exp_add_error {r : ℝ}
    (hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant)) (x y : GleasonLieAlgebra D) {L₁ L₂ : ℝ}
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hx : ∀ t : ℝ, D.gauge ((toOneParameter D x).eval t) ≤ L₁*|t|)
    (hy : ∀ t : ℝ, D.gauge ((toOneParameter D y).eval t) ≤ L₂*|t|)
    (hsmall : L₁+L₂ ≤ r) :
    D.metric.dist (exp D x*exp D y) (exp D (x+y)) ≤ 4*D.constant*L₁*L₂ := by
  change D.metric.dist ((toOneParameter D x).eval 1*(toOneParameter D y).eval 1)
    ((D.trotterSum (toOneParameter D x) (toOneParameter D y)).eval 1) ≤ _
  simpa only [OneParameter.productApprox,Nat.cast_one,div_one,pow_one,abs_one,one_pow,mul_one] using
    D.trotterSum_distance hp hr (toOneParameter D x) (toOneParameter D y) hL₁ hL₂ hx hy 1
      (by simpa only [abs_one,mul_one] using hsmall) 1 (by omega)
end GleasonLieAlgebra
end DirectedCycles
