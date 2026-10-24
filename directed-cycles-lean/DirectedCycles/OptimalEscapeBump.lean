import DirectedCycles.RegularizedEscapeDistance
import Mathlib.Data.Finset.Max

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

/-- The regularized bump at the actual minimum distance to the complement.
Keeping the attaining point makes the later improvement of the Lipschitz
constant an exact inequality, without changing the chosen bump. -/
theorem exists_optimal_escape_bump (A : Finset G) (hA : (1 : G) ∈ A)
    (hi : (A : Set G)⁻¹ = A) (hproper : ∃ b : G, b ∉ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, ∃ b : G, ε ≤ r ∧ b ∉ A ∧ regularizedEscapeDistance A ε b = r ∧
      (∀ g : G, g ∉ A → r ≤ regularizedEscapeDistance A ε g) ∧
      ∃ φ : G → ℝ, (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
        (∀ x ∈ A, φ x = 1) ∧
        (∀ x, x ∉ (A : Set G)^2 → φ x = 0) ∧
        (∀ g x, |φ (g⁻¹*x)-φ x| ≤ regularizedEscapeDistance A ε g / r) := by
  classical
  have hcomp : (Aᶜ).Nonempty := by
    obtain ⟨b,hb⟩ := hproper
    exact ⟨b,Finset.mem_compl.mpr hb⟩
  obtain ⟨b,hb,hmin⟩ := (Aᶜ).exists_min_image (regularizedEscapeDistance A ε) hcomp
  have hbA : b ∉ A := by simpa using hb
  let r := regularizedEscapeDistance A ε b
  have hrε : ε ≤ r := le_regularizedEscapeDistance_of_not_mem hA hε.le hbA
  have hr : 0 < r := hε.trans_le hrε
  have hsep : ∀ g : G, g ∉ A → r ≤ regularizedEscapeDistance A ε g := by
    intro g hg
    exact hmin g (by simpa using hg)
  refine ⟨r,b,hrε,hbA,rfl,hsep,?_⟩
  exact exists_norm_bump (regularizedEscapeDistance_nonneg hA hε.le)
    (regularizedEscapeDistance_one hA hε.le)
    (regularizedEscapeDistance_mul_le hA hε.le)
    (regularizedEscapeDistance_inv hi ε) A ⟨1,hA⟩ hr hsep
end DirectedCycles
