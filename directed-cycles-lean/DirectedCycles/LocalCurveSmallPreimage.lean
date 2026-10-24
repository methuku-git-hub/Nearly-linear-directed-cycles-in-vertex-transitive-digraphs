import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {H : Type*} [TopologicalSpace H] [T2Space H]

/-- Compactness of the actual closed parameter segment isolates the identity
from every parameter annulus, using only continuity on that segment. -/
theorem local_curve_small_preimage (f : ℝ → H) (e : H)
    (hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hgap : ∀ t : ℝ, 0 < |t| → |t| ≤ 1 → f t ≠ e)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set H, IsOpen V ∧ e ∈ V ∧ ∀ t : ℝ, |t| ≤ 1 → f t ∈ V → |t| < ε := by
  let B : Set ℝ := Set.Icc (-1) (-ε) ∪ Set.Icc ε 1
  let V : Set H := (f '' B)ᶜ
  have hBc : IsCompact B := isCompact_Icc.union isCompact_Icc
  have hBsub : B ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    rcases ht with ht | ht
    · exact ⟨ht.1,by linarith [ht.2]⟩
    · exact ⟨by linarith [ht.1],ht.2⟩
  have hVo : IsOpen V := (hBc.image_of_continuousOn (hcont.mono hBsub)).isClosed.isOpen_compl
  have hVe : e ∈ V := by
    rintro ⟨t,ht,he⟩
    have hb : ε ≤ |t| ∧ |t| ≤ 1 := by
      rcases ht with ht | ht
      · rw [abs_of_neg (by linarith [ht.2] : t < 0)]
        constructor <;> linarith [ht.1,ht.2]
      · rw [abs_of_pos (by linarith [ht.1] : 0 < t)]
        constructor <;> linarith [ht.1,ht.2]
    exact hgap t (lt_of_lt_of_le hε hb.1) hb.2 he
  refine ⟨V,hVo,hVe,?_⟩
  intro t ht hv
  by_contra hn
  have he : ε ≤ |t| := le_of_not_gt hn
  have hb : t ∈ B := by
    by_cases h : 0 ≤ t
    · right
      rw [abs_of_nonneg h] at ht he
      exact ⟨he,ht⟩
    · left
      rw [abs_of_neg (lt_of_not_ge h)] at ht he
      exact ⟨by linarith,by linarith⟩
  exact hv ⟨t,hb,rfl⟩
end DirectedCycles
