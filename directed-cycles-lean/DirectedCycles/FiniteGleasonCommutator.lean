import DirectedCycles.ConvolutionPowerSupport
import DirectedCycles.UnregularizedEscapeBump
import DirectedCycles.EscapeNormDerivatives

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

/-- The finite global commutator estimate from the proved product bound and
first trapping condition. Its explicit polynomial constant is immaterial to
the structural theorem, but every factor is retained here. -/
theorem finite_gleason_commutator_of_product (A : Finset G) {K : ℝ}
    (hK : 1 ≤ K) (hA : IsApproximateSubgroup K (A : Set G))
    (C : ℕ) (hC : 0 < C)
    (hfirst : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ (A : Set G)^100) → x ∈ A)
    {P : ℝ} (hP : 0 < P)
    (hp : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum)
    {g h : G} (hg : g ∈ (A : Set G)^10) (hh : h ∈ (A : Set G)^10) :
    escapeNorm A (g⁻¹*h⁻¹*g*h) ≤
      (2*(C : ℝ)^2*K^11*P^2)*escapeNorm A g*escapeNorm A h := by
  have hK0 : 0 ≤ K := by linarith
  have hCr : 0 ≤ (C : ℝ) := Nat.cast_nonneg C
  have hA4 : (1 : G) ∈ (A : Set G)^4 := Set.one_mem_pow hA.one_mem
  have htrap4 : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ (A : Set G)^4) → x ∈ A := by
    intro x hx
    apply hfirst
    intro j hj hjC
    exact (Set.pow_subset_pow_right hA.one_mem (by omega : 4 ≤ 100)) (hx j hj hjC)
  have hconj : ∀ y ∈ (A : Set G)^12, ∀ z ∈ (A : Set G), y⁻¹*z*y ∈ (A : Set G)^100 := by
    intro y hy z hz
    have hyi : y⁻¹ ∈ (A : Set G)^12 := by
      have he : ((A : Set G)^12)⁻¹ = (A : Set G)^12 := by rw [← inv_pow, hA.inv_eq_self]
      have hy' : y⁻¹ ∈ ((A : Set G)^12)⁻¹ := Set.inv_mem_inv.mpr hy
      simpa only [he] using hy'
    have hz' : z ∈ (A : Set G)^1 := by simpa using hz
    have hm : y⁻¹*z*y ∈ (A : Set G)^25 := by
      have ht := Set.mul_mem_mul (Set.mul_mem_mul hyi hz') hy
      simpa only [← pow_add] using ht
    exact (Set.pow_subset_pow_right hA.one_mem (by omega : 25 ≤ 100)) hm
  have heconj : ∀ y ∈ (A : Set G)^12, ∀ z : G,
      escapeNorm A (y⁻¹*z*y) ≤ (C : ℝ)*escapeNorm A z := by
    intro y hy z
    exact escapeNorm_conjugate_of_trapping hA.one_mem C hC hfirst y (hconj y hy) z
  obtain ⟨φ,hφ,hφA,hφs,hφlip⟩ := exists_unregularized_escape_bump A hA.one_mem hA.inv_eq_self hP hp
  have hφd : ∀ x, derivativeNorm φ x ≤ P*escapeNorm A x := by
    intro x
    apply (derivativeNorm_le_iff _ _ (mul_nonneg hP.le (escapeNorm_nonneg hA.one_mem x))).2
    intro y
    exact hφlip x y
  let f := normalizedConvolution A φ φ
  have hf1 : 1 ≤ f 1 := normalizedConvolution_one A hA.one_mem hA.inv_eq_self
    (fun x => (hφ x).1) (fun x => (hφ x).1) hφA hφA
  have hfs : ∀ x, x ∉ (A : Set G)^4 → f x = 0 :=
    fun _ hx => normalizedConvolution_support hφs hφs hx
  have he : ∀ x, escapeNorm A x ≤ (C : ℝ)*derivativeNorm f x :=
    escapeNorm_le_mul_derivativeNorm hA4 C hC htrap4 f hf1 hfs
  have htwo : ∀ a ∈ (A : Set G)^10, ∀ b : G,
      derivativeNorm (groupDerivative a f) b ≤
        (C : ℝ)*K^11*P^2*escapeNorm A a*escapeNorm A b := by
    intro a ha b
    have hb0 := escapeNorm_nonneg hA.one_mem b
    have ha0 := escapeNorm_nonneg hA.one_mem a
    have hbnd : ∀ y ∈ (A : Set G)^12, derivativeNorm φ (y⁻¹*b*y) ≤ P*((C : ℝ)*escapeNorm A b) := by
      intro y hy
      exact (hφd _).trans (mul_le_mul_of_nonneg_left (heconj y hy b) hP.le)
    have ht := derivativeNorm_twice_normalizedConvolution_power_le hA hφs ha
      (mul_nonneg hP.le (mul_nonneg hCr hb0)) hbnd
    calc
      derivativeNorm (groupDerivative a f) b ≤ K^11*derivativeNorm φ a*(P*((C : ℝ)*escapeNorm A b)) := ht
      _ ≤ K^11*(P*escapeNorm A a)*(P*((C : ℝ)*escapeNorm A b)) := by gcongr; exact hφd a
      _ = (C : ℝ)*K^11*P^2*escapeNorm A a*escapeNorm A b := by ring
  have hc := derivativeNorm_commutator_le f g h
  have h1 := htwo h hh g
  have h2 := htwo g hg h
  have hsum : derivativeNorm f (g⁻¹*h⁻¹*g*h) ≤
      2*(C : ℝ)*K^11*P^2*escapeNorm A g*escapeNorm A h := by nlinarith
  calc
    escapeNorm A (g⁻¹*h⁻¹*g*h) ≤ (C : ℝ)*derivativeNorm f (g⁻¹*h⁻¹*g*h) := he _
    _ ≤ (C : ℝ)*(2*(C : ℝ)*K^11*P^2*escapeNorm A g*escapeNorm A h) :=
      mul_le_mul_of_nonneg_left hsum hCr
    _ = (2*(C : ℝ)^2*K^11*P^2)*escapeNorm A g*escapeNorm A h := by ring
end DirectedCycles
