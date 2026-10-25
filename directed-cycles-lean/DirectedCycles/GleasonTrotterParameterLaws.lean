module

public import DirectedCycles.GleasonTrotterLimit

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace OneParameter
variable {G : Type*} [Group G] [TopologicalSpace G]

@[simp] theorem productApprox_zero (φ ψ : OneParameter G) (n : ℕ) :
    φ.productApprox ψ 0 n = 1 := by simp [productApprox]

theorem productLimit_zero [T2Space G] (φ ψ : OneParameter G) :
    φ.productLimit ψ 0 = 1 := by
  have h : Tendsto (φ.productApprox ψ 0) atTop (𝓝 (1 : G)) := by
    have he : φ.productApprox ψ 0 = (fun _ : ℕ => (1 : G)) := funext (φ.productApprox_zero ψ)
    rw [he]
    exact tendsto_const_nhds
  exact h.limUnder_eq

/-- Integer reparameterisation corresponds exactly to a subsequence of
finite product approximations and an outer power. -/
theorem productApprox_nat_mul (φ ψ : OneParameter G) (t : ℝ) (k n : ℕ)
    (hk : 0 < k) (hn : 0 < n) :
    φ.productApprox ψ ((k : ℝ)*t) (k*n) = (φ.productApprox ψ t n)^k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : ((k : ℝ)*t)/((k*n : ℕ) : ℝ) = t/(n : ℝ) := by
    rw [Nat.cast_mul]
    field_simp
  dsimp only [productApprox]
  rw [hid,← pow_mul,Nat.mul_comm n k]

/-- Negating a parameter reverses the product, up to an explicit small
conjugating factor. -/
theorem productApprox_neg (φ ψ : OneParameter G) (t : ℝ) (n : ℕ) :
    (φ.productApprox ψ (-t) n)⁻¹ =
      ψ.eval (t/(n : ℝ))*φ.productApprox ψ t n*(ψ.eval (t/(n : ℝ)))⁻¹ := by
  dsimp only [productApprox]
  rw [neg_div,φ.eval_neg,ψ.eval_neg,← inv_pow, mul_inv_rev,inv_inv,inv_inv]
  have hc : ψ.eval (t/(n : ℝ))*φ.eval (t/(n : ℝ)) =
      ψ.eval (t/(n : ℝ))*(φ.eval (t/(n : ℝ))*ψ.eval (t/(n : ℝ)))*(ψ.eval (t/(n : ℝ)))⁻¹ := by group
  rw [hc]
  exact conj_pow
end OneParameter

namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    {r : ℝ}
    (hpow : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r →
      (n : ℝ)*D.gauge h ≤ r → D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h)
    (hr : r ≤ 1/(8*D.constant))
    (φ ψ : OneParameter G) {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hφ : ∀ t : ℝ, D.gauge (φ.eval t) ≤ L₁*|t|)
    (hψ : ∀ t : ℝ, D.gauge (ψ.eval t) ≤ L₂*|t|)
include hpow hr hL₁ hφ hψ

/-- Integer parameter scaling of the limit follows from actual convergent
subsequences, not from an assumed homomorphism law. -/
theorem productLimit_nat_mul (t : ℝ) (k : ℕ) (hk : 0 < k)
    (ht : (L₁+L₂)*|t| ≤ r) (hkt : (L₁+L₂)*|(k : ℝ)*t| ≤ r) :
    φ.productLimit ψ ((k : ℝ)*t) = (φ.productLimit ψ t)^k := by
  let : MetricSpace G := D.compatibleMetric
  have hmul : Tendsto (fun n : ℕ => k*n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id
  have hs := (D.productLimit_tendsto hpow hr φ ψ hL₁ hφ hψ ((k : ℝ)*t) hkt).comp hmul
  have hp := (D.productLimit_tendsto hpow hr φ ψ hL₁ hφ hψ t ht).pow k
  have he : (fun n : ℕ => φ.productApprox ψ ((k : ℝ)*t) (k*n)) =ᶠ[atTop]
      (fun n : ℕ => (φ.productApprox ψ t n)^k) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact φ.productApprox_nat_mul ψ t k n hk (by omega)
  exact tendsto_nhds_unique hs (hp.congr' he.symm)

/-- Negation of the actual limit is group inversion, because the
conjugating factors tend to the identity. -/
theorem productLimit_neg (t : ℝ) (ht : (L₁+L₂)*|t| ≤ r) :
    φ.productLimit ψ (-t) = (φ.productLimit ψ t)⁻¹ := by
  let : MetricSpace G := D.compatibleMetric
  have hnt : (L₁+L₂)*|-t| ≤ r := by simpa only [abs_neg] using ht
  have hminus := (D.productLimit_tendsto hpow hr φ ψ hL₁ hφ hψ (-t) hnt).inv
  have hy : Tendsto (fun n : ℕ => ψ.eval (t/(n : ℝ))) atTop (𝓝 (1 : G)) := by
    simpa only [Function.comp_def,ψ.eval_zero] using ψ.continuous_eval.continuousAt.tendsto.comp
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have htend := D.productLimit_tendsto hpow hr φ ψ hL₁ hφ hψ t ht
  have he : (fun n : ℕ => (φ.productApprox ψ (-t) n)⁻¹) =
      (fun n : ℕ => ψ.eval (t/(n : ℝ))*φ.productApprox ψ t n*(ψ.eval (t/(n : ℝ)))⁻¹) :=
    funext (fun n => φ.productApprox_neg ψ t n)
  have hright := (hy.mul htend).mul hy.inv
  simp only [one_mul,inv_one,mul_one] at hright
  have hi : (φ.productLimit ψ (-t))⁻¹ = φ.productLimit ψ t := by
    rw [he] at hminus
    exact tendsto_nhds_unique hminus hright
  exact inv_eq_iff_eq_inv.mp hi
end GleasonMetricData
end DirectedCycles
