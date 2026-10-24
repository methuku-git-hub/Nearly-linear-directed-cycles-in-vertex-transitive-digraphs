import DirectedCycles.StrongApproximateGroups
import DirectedCycles.SubgroupEscapeNorm

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

theorem strong_approximate_product_all {K : ℕ} {A : Finset G}
    (hA : IsStrongFiniteApproximateGroup K A) (l : List G) :
    escapeNorm A l.prod ≤
      (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*(l.map (escapeNorm A)).sum := by
  by_cases hK : 2 ≤ K
  · exact strong_approximate_product hA hK l
  · have hK1 : K = 1 := by have := hA.one_le; omega
    subst K
    have hp := small_approximate_escape_product hA.approximate (by norm_num) l
    have hs : 0 ≤ (l.map (escapeNorm (A : Set G))).sum :=
      List.sum_nonneg (by simpa using fun g (_ : g ∈ l) => escapeNorm_nonneg hA.approximate.one_mem g)
    norm_num
    nlinarith

theorem strong_approximate_commutator_all {K : ℕ} {A : Finset G}
    (hA : IsStrongFiniteApproximateGroup K A)
    {g h : G} (hg : g ∈ (A : Set G)^10) (hh : h ∈ (A : Set G)^10) :
    let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
    escapeNorm A (g⁻¹*h⁻¹*g*h) ≤
      (2*(1000 : ℝ)^2*(K : ℝ)^11*P^2)*escapeNorm A g*escapeNorm A h := by
  by_cases hK : 2 ≤ K
  · exact strong_approximate_commutator hA hK hg hh
  · have hK1 : K = 1 := by have := hA.one_le; omega
    subst K
    obtain ⟨H,hH⟩ := approximate_subgroup_lt_two (A : Set G) 1 (by simpa using hA.approximate) (by norm_num)
    have hgH : g ∈ H := set_power_subset_subgroup H 10 (by simpa only [hH] using hg)
    have hhH : h ∈ H := set_power_subset_subgroup H 10 (by simpa only [hH] using hh)
    have hcH : g⁻¹*h⁻¹*g*h ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hgH) (H.inv_mem hhH)) hgH) hhH
    have hc := escapeNorm_subgroup_eq_zero hcH
    have hgz := escapeNorm_subgroup_eq_zero hgH
    simp only [hH] at hc hgz
    simp [hc,hgz]

omit [Fintype G] in
/-- The conjugation estimate holds for every g; only the conjugating element
needs to lie in the tenth power. -/
theorem strong_approximate_conjugation {K : ℕ} {A : Finset G}
    (hA : IsStrongFiniteApproximateGroup K A) {h : G} (hh : h ∈ (A : Set G)^10) (g : G) :
    escapeNorm A (h⁻¹*g*h) ≤ 1000*escapeNorm A g := by
  obtain ⟨S,hSi,hsmall,hfirst,hsecond⟩ := hA.trapping
  have hhi : h⁻¹ ∈ (A : Set G)^10 := by
    have he : ((A : Set G)^10)⁻¹ = (A : Set G)^10 := by rw [← inv_pow,hA.approximate.inv_eq_self]
    have hm : h⁻¹ ∈ ((A : Set G)^10)⁻¹ := Set.inv_mem_inv.mpr hh
    simpa only [he] using hm
  have hconj : ∀ x ∈ (A : Set G), h⁻¹*x*h ∈ (A : Set G)^100 := by
    intro x hx
    have hx1 : x ∈ (A : Set G)^1 := by simpa using hx
    have hp : h⁻¹*x*h ∈ (A : Set G)^21 := by
      simpa only [← pow_add] using Set.mul_mem_mul (Set.mul_mem_mul hhi hx1) hh
    exact (Set.pow_subset_pow_right hA.approximate.one_mem (by omega : 21 ≤ 100)) hp
  exact escapeNorm_conjugate_of_trapping hA.approximate.one_mem 1000 (by omega) hfirst h hconj g
end DirectedCycles
