import DirectedCycles.StrongEscapeEstimates

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The zero set of the actual escape norm is a subgroup once the product
estimate is available. It is not postulated to be a subgroup. -/
noncomputable def zeroEscapeSubgroup (A : Set G) (hA : 1 ∈ A) (hi : A⁻¹ = A)
    (P : ℝ) (hp : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum) : Subgroup G where
  carrier := {g | escapeNorm A g = 0}
  one_mem' := escapeNorm_one hA
  mul_mem' := by
    intro a b ha hb
    change escapeNorm A a = 0 at ha
    change escapeNorm A b = 0 at hb
    apply le_antisymm _ (escapeNorm_nonneg hA (a*b))
    have h := hp [a,b]
    simpa only [List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ha, hb, zero_add, mul_zero] using h
  inv_mem' := by
    intro a ha
    change escapeNorm A a⁻¹ = 0
    rw [escapeNorm_inv hi,ha]

@[simp] theorem mem_zeroEscapeSubgroup (A : Set G) (hA : 1 ∈ A) (hi : A⁻¹ = A)
    (P : ℝ) (hp : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum) (g : G) :
    g ∈ zeroEscapeSubgroup A hA hi P hp ↔ escapeNorm A g = 0 := Iff.rfl

theorem zeroEscapeSubgroup_subset (A : Set G) (hA : 1 ∈ A) (hi : A⁻¹ = A)
    (P : ℝ) (hp : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum) :
    (zeroEscapeSubgroup A hA hi P hp : Set G) ⊆ A := by
  intro g hg
  apply mem_of_escapeNorm_lt_one hA
  change escapeNorm A g = 0 at hg
  rw [hg]
  norm_num

theorem zeroEscapeSubgroup_normalized (A : Set G) (hA : 1 ∈ A) (hi : A⁻¹ = A)
    (P : ℝ) (hp : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum)
    (B : Set G) (hBi : B⁻¹ = B) (C : ℝ)
    (hc : ∀ b ∈ B, ∀ x, escapeNorm A (b⁻¹*x*b) ≤ C*escapeNorm A x) :
    B ⊆ Subgroup.normalizer (zeroEscapeSubgroup A hA hi P hp : Set G) := by
  intro b hb
  apply Subgroup.mem_set_normalizer_iff''.2
  have hbi : b⁻¹ ∈ B := by
    have h : b⁻¹ ∈ B⁻¹ := Set.inv_mem_inv.mpr hb
    simpa only [hBi] using h
  intro x
  change escapeNorm A x = 0 ↔ escapeNorm A (b⁻¹*x*b) = 0
  constructor
  · intro hx
    apply le_antisymm _ (escapeNorm_nonneg hA _)
    simpa [hx] using hc b hb x
  · intro hx
    apply le_antisymm _ (escapeNorm_nonneg hA x)
    have h := hc b⁻¹ hbi (b⁻¹*x*b)
    rw [hx,mul_zero] at h
    simpa [mul_assoc] using h

variable [Fintype G]

/-- The exact finite zero-escape subgroup and its full normalizing set. -/
theorem strong_approximate_zero_subgroup {K : ℕ} {A : Finset G}
    (hA : IsStrongFiniteApproximateGroup K A) :
    ∃ H : Subgroup G, (∀ g, g ∈ H ↔ escapeNorm A g = 0) ∧
      (H : Set G) ⊆ A ∧ (A : Set G)^10 ⊆ Subgroup.normalizer (H : Set G) := by
  let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
  have hp : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum := strong_approximate_product_all hA
  let H := zeroEscapeSubgroup (A : Set G) hA.approximate.one_mem hA.approximate.inv_eq_self P hp
  refine ⟨H,fun _ => Iff.rfl,zeroEscapeSubgroup_subset _ _ _ _ _,?_⟩
  exact zeroEscapeSubgroup_normalized (A : Set G) hA.approximate.one_mem hA.approximate.inv_eq_self P hp
    ((A : Set G)^10) (by rw [← inv_pow,hA.approximate.inv_eq_self]) 1000
    (fun b hb x => strong_approximate_conjugation hA hb x)
end DirectedCycles
