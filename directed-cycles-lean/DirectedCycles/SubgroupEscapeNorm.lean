import DirectedCycles.EscapeNorm
import DirectedCycles.ApproximateSmallConstant

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

theorem escapeNorm_subgroup_eq_zero {H : Subgroup G} {g : G} (hg : g ∈ H) :
    escapeNorm (H : Set G) g = 0 :=
  (escapeNorm_eq_zero_iff H.one_mem g).2 (fun n => H.pow_mem hg n)

theorem escapeNorm_subgroup_mul_le (H : Subgroup G) (g h : G) :
    escapeNorm (H : Set G) (g*h) ≤ escapeNorm (H : Set G) g + escapeNorm (H : Set G) h := by
  by_cases hg : g ∈ H
  · by_cases hh : h ∈ H
    · simp [escapeNorm_subgroup_eq_zero hg, escapeNorm_subgroup_eq_zero hh,
        escapeNorm_subgroup_eq_zero (H.mul_mem hg hh)]
    · rw [escapeNorm_subgroup_eq_zero hg, escapeNorm_eq_one_of_not_mem H.one_mem hh, zero_add]
      exact escapeNorm_le_one H.one_mem (g*h)
  · rw [escapeNorm_eq_one_of_not_mem H.one_mem hg]
    exact (escapeNorm_le_one H.one_mem (g*h)).trans (le_add_of_nonneg_right (escapeNorm_nonneg H.one_mem h))

theorem escapeNorm_subgroup_prod_le (H : Subgroup G) (l : List G) :
    escapeNorm (H : Set G) l.prod ≤ (l.map (escapeNorm (H : Set G))).sum := by
  induction l with
  | nil => simp [escapeNorm_one H.one_mem]
  | cons g l ih =>
    simpa using (escapeNorm_subgroup_mul_le H g l.prod).trans (add_le_add le_rfl ih)

theorem set_power_subset_subgroup (H : Subgroup G) (n : ℕ) : (H : Set G)^n ⊆ H := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rintro x ⟨a,ha,b,hb,rfl⟩
    exact H.mul_mem (ih ha) hb

theorem small_approximate_escape_product {A : Finset G} {K : ℝ}
    (hA : IsApproximateSubgroup K (A : Set G)) (hK : K < 2) (l : List G) :
    escapeNorm A l.prod ≤ (l.map (escapeNorm (A : Set G))).sum := by
  obtain ⟨H,hH⟩ := approximate_subgroup_lt_two (A : Set G) K hA hK
  simpa only [hH] using escapeNorm_subgroup_prod_le H l
end DirectedCycles
