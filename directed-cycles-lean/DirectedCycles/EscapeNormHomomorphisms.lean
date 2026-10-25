module

public import DirectedCycles.EscapeNormTrapping
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G H : Type*} [Group G] [Group H]

theorem escapeNorm_preimage (q : G →* H) (B : Set H) (g : G) :
    escapeNorm (q ⁻¹' B) g = escapeNorm B (q g) := by
  unfold escapeNorm
  congr 1
  ext x
  simp only [escapeValues, Set.mem_ofPred_eq, Set.mem_preimage, map_pow]

theorem escapeNorm_image_le (q : G →* H) {A : Set G} (hA : 1 ∈ A) (g : G) :
    escapeNorm (q '' A) (q g) ≤ escapeNorm A g := by
  apply le_csInf (escapeValues_nonempty hA g)
  rintro x ⟨n,hn,rfl⟩
  apply escapeNorm_le_of_powers
  intro i hi
  exact ⟨g^i,hn i hi,by rw [map_pow]⟩

theorem mem_square_of_map_mem_image (q : G →* H) {A : Set G}
    (hker : (q.ker : Set G) ⊆ A) {g : G} (hg : q g ∈ q '' A) : g ∈ A^2 := by
  obtain ⟨a,ha,he⟩ := hg
  have hk : a⁻¹*g ∈ q.ker := by
    change q (a⁻¹*g) = 1
    simp [map_mul, map_inv, he]
  rw [pow_two]
  exact ⟨a,ha,a⁻¹*g,hker hk,by simp⟩

/-- Quotienting by a kernel lying in A loses at most the first-trapping constant
in the escape norm. -/
theorem escapeNorm_le_image_of_trapping (q : G →* H) {A : Set G} (hA : 1 ∈ A)
    (hker : (q.ker : Set G) ⊆ A) (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^4) → x ∈ A)
    (g : G) : escapeNorm A g ≤ (C : ℝ)*escapeNorm (q '' A) (q g) := by
  rw [← escapeNorm_preimage]
  have hpre1 : 1 ∈ q ⁻¹' (q '' A) := by
    exact ⟨1,hA,by simp⟩
  apply escapeNorm_le_mul_of_trapping hpre1 C hC
  intro x hx
  apply htrap
  intro j hj hjC
  exact (Set.pow_subset_pow_right hA (by omega : 2 ≤ 4))
    (mem_square_of_map_mem_image q hker (hx j hj hjC))

/-- Removing exactly the zero-escape kernel leaves no nontrivial cyclic
subgroup contained in the image approximate set. -/
theorem quotient_no_small_subgroups (q : G →* H) (hq : Function.Surjective q)
    {A : Set G} (hA : 1 ∈ A) (hker : (q.ker : Set G) ⊆ A)
    (hzero : ∀ g, escapeNorm A g = 0 → g ∈ q.ker)
    (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^4) → x ∈ A) :
    ∀ y : H, (∀ n : ℕ, y^n ∈ q '' A) → y = 1 := by
  intro y hy
  obtain ⟨g,rfl⟩ := hq y
  have hB1 : 1 ∈ q '' A := ⟨1,hA,by simp⟩
  have he := (escapeNorm_eq_zero_iff hB1 (q g)).2 hy
  have hle := escapeNorm_le_image_of_trapping q hA hker C hC htrap g
  rw [he,mul_zero] at hle
  exact hzero g (le_antisymm hle (escapeNorm_nonneg hA g))
end DirectedCycles
