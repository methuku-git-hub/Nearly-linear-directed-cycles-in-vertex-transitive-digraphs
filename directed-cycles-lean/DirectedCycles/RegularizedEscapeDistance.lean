import DirectedCycles.EscapeNorm
import DirectedCycles.NormSetBump

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

noncomputable def regularizedEscapeDistance (A : Set G) (ε : ℝ) : G → ℝ :=
  wordNorm (fun g => escapeNorm A g + ε)

theorem regularizedEscapeDistance_nonneg {A : Set G} (hA : 1 ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) (g : G) : 0 ≤ regularizedEscapeDistance A ε g :=
  wordNorm_nonneg (fun x => add_nonneg (escapeNorm_nonneg hA x) hε) g

theorem regularizedEscapeDistance_one {A : Set G} (hA : 1 ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) : regularizedEscapeDistance A ε 1 = 0 :=
  wordNorm_one (fun x => add_nonneg (escapeNorm_nonneg hA x) hε)

theorem regularizedEscapeDistance_le {A : Set G} (hA : 1 ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) (g : G) :
    regularizedEscapeDistance A ε g ≤ escapeNorm A g + ε :=
  wordNorm_le_weight (fun x => add_nonneg (escapeNorm_nonneg hA x) hε) g

theorem regularizedEscapeDistance_mul_le {A : Set G} (hA : 1 ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) (g h : G) :
    regularizedEscapeDistance A ε (g*h) ≤
      regularizedEscapeDistance A ε g + regularizedEscapeDistance A ε h :=
  wordNorm_mul_le (fun x => add_nonneg (escapeNorm_nonneg hA x) hε) g h

theorem regularizedEscapeDistance_inv {A : Set G} (hi : A⁻¹ = A) (ε : ℝ) (g : G) :
    regularizedEscapeDistance A ε g⁻¹ = regularizedEscapeDistance A ε g :=
  wordNorm_inv (fun x => by rw [escapeNorm_inv hi]) g

theorem le_regularizedEscapeDistance_of_not_mem {A : Set G} (hA : 1 ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) {g : G} (hg : g ∉ A) :
    ε ≤ regularizedEscapeDistance A ε g := by
  apply le_wordNorm_of_weight_lower hε
  · intro x
    exact le_add_of_nonneg_left (escapeNorm_nonneg hA x)
  · intro he
    exact hg (he ▸ hA)

/-- The regularized bump needed for BGT's product estimate, proved from the
actual escape norm and actual infimum of word costs. -/
theorem exists_regularized_escape_bump (A : Finset G) (hA : (1 : G) ∈ A)
    (hi : (A : Set G)⁻¹ = A) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : G → ℝ, (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ A, φ x = 1) ∧
      (∀ x, x ∉ (A : Set G)^2 → φ x = 0) ∧
      (∀ g x, |φ (g⁻¹*x)-φ x| ≤ regularizedEscapeDistance A ε g / ε) := by
  exact exists_norm_bump (regularizedEscapeDistance_nonneg hA hε.le)
    (regularizedEscapeDistance_one hA hε.le)
    (regularizedEscapeDistance_mul_le hA hε.le)
    (regularizedEscapeDistance_inv hi ε)
    A ⟨1,hA⟩ hε (fun _ hg => le_regularizedEscapeDistance_of_not_mem hA hε.le hg)
end DirectedCycles
