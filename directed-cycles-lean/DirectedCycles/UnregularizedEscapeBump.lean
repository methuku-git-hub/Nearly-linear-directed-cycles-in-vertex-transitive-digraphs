module

public import DirectedCycles.RegularizedEscapeDistance

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

theorem wordNorm_escape_separation {A : Set G} (hA : 1 ∈ A) {P : ℝ} (hP : 0 < P)
    (hp : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum)
    {g : G} (hg : g ∉ A) : 1/P ≤ wordNorm (escapeNorm A) g := by
  apply le_csInf (wordCosts_nonempty _ g)
  rintro x ⟨l,hl,rfl⟩
  apply (div_le_iff₀ hP).2
  have h := hp l
  rw [hl, escapeNorm_eq_one_of_not_mem hA hg] at h
  simpa [mul_comm] using h

/-- Once the product estimate has been proved, no regularization is needed
for the bump used to obtain the commutator estimate. -/
theorem exists_unregularized_escape_bump (A : Finset G) (hA : (1 : G) ∈ A)
    (hi : (A : Set G)⁻¹ = A) {P : ℝ} (hP : 0 < P)
    (hp : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum) :
    ∃ φ : G → ℝ, (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ A, φ x = 1) ∧
      (∀ x, x ∉ (A : Set G)^2 → φ x = 0) ∧
      (∀ g x, |φ (g⁻¹*x)-φ x| ≤ P*escapeNorm A g) := by
  have hw := escapeNorm_nonneg hA
  obtain ⟨φ,hφ,hφA,hφs,hφlip⟩ := exists_norm_bump (wordNorm_nonneg hw) (wordNorm_one hw)
    (wordNorm_mul_le hw) (wordNorm_inv (escapeNorm_inv hi)) A ⟨1,hA⟩ (by positivity : 0 < 1/P)
    (fun _ hg => wordNorm_escape_separation hA hP hp hg)
  refine ⟨φ,hφ,hφA,hφs,?_⟩
  intro g x
  apply (hφlip g x).trans
  simp only [one_div, div_inv_eq_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right (wordNorm_le_weight hw g) hP.le
end DirectedCycles
