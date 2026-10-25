module

public import DirectedCycles.NormalizedConvolution

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

theorem groupDerivative_support_power {A : Set G} (hA : 1 ∈ A) {f : G → ℝ}
    (hfs : ∀ x, x ∉ A^2 → f x = 0) {p : ℕ} {g : G} (hg : g ∈ A^p)
    {x : G} (hx : x ∉ A^(p+2)) : groupDerivative g f x = 0 := by
  have hxs : x ∉ A^2 := fun h => hx ((Set.pow_subset_pow_right hA (by omega : 2 ≤ p+2)) h)
  have hxg : g⁻¹*x ∉ A^2 := by
    intro h
    apply hx
    have hh : g*(g⁻¹*x) ∈ A^p*A^2 := Set.mul_mem_mul hg h
    simpa [← pow_add] using hh
  simp [groupDerivative, leftShift, hfs x hxs, hfs (g⁻¹*x) hxg]

variable [Fintype G]

theorem derivativeNorm_twice_normalizedConvolution_power_le {A : Finset G} {K : ℝ}
    (hA : IsApproximateSubgroup K (A : Set G)) {f k : G → ℝ}
    (hfs : ∀ x, x ∉ (A : Set G)^2 → f x = 0)
    {p : ℕ} {g h : G} (hg : g ∈ (A : Set G)^p) {r : ℝ} (hr : 0 ≤ r)
    (hk : ∀ y ∈ (A : Set G)^(p+2), derivativeNorm k (y⁻¹*h*y) ≤ r) :
    derivativeNorm (groupDerivative g (normalizedConvolution A f k)) h ≤
      K^(p+1)*derivativeNorm f g*r := by
  classical
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨1,hA.one_mem⟩
  have hc : ((A^(p+2)).card : ℝ) ≤ K^(p+1)*A.card := by
    simpa using hA.card_pow_le (n := p+2)
  have hs : ∀ y, y ∉ A^(p+2) → groupDerivative g f y = 0 := by
    intro y hy
    apply groupDerivative_support_power hA.one_mem hfs hg
    simpa only [← Finset.coe_pow, Finset.mem_coe] using hy
  have hk' : ∀ y ∈ A^(p+2), derivativeNorm k (y⁻¹*h*y) ≤ r := by
    intro y hy
    apply hk
    simpa only [← Finset.coe_pow, Finset.mem_coe] using hy
  have hd0 := derivativeNorm_nonneg f g
  unfold normalizedConvolution
  rw [groupDerivative_smul, derivativeNorm_smul, abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ (A.card : ℝ)⁻¹*((A^(p+2)).card*derivativeNorm f g*r) :=
      mul_le_mul_of_nonneg_left (derivativeNorm_twice_convolution_le g h (A^(p+2))
        hd0 hr hs le_rfl hk') (by positivity)
    _ ≤ (A.card : ℝ)⁻¹*((K^(p+1)*A.card)*derivativeNorm f g*r) := by gcongr
    _ = K^(p+1)*derivativeNorm f g*r := by field_simp
end DirectedCycles
