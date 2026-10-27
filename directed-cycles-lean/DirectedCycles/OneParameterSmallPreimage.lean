module

public import DirectedCycles.CentralCurveLocalNormal

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]

/-- Excluding the compact parameter annulus gives an actual target neighbourhood
whose bounded curve preimages all have arbitrarily small parameter. -/
theorem one_parameter_small_preimage (φ : ℝ → H) (hcont : Continuous φ)
    {R ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ t : ℝ, 0 < |t| → |t| ≤ R → φ t ≠ 1) :
    ∃ V : Set H, IsOpen V ∧ (1 : H) ∈ V ∧
      ∀ t : ℝ, |t| ≤ R → φ t ∈ V → |t| < ε := by
  let B : Set ℝ := Set.Icc (-R) (-ε) ∪ Set.Icc ε R
  let V : Set H := (φ '' B)ᶜ
  have hBc : IsCompact B := isCompact_Icc.union isCompact_Icc
  have hVo : IsOpen V := (hBc.image hcont).isClosed.isOpen_compl
  have hV1 : (1 : H) ∈ V := by
    rintro ⟨t,ht,he⟩
    have hb : ε ≤ |t| ∧ |t| ≤ R := by
      rcases ht with ht | ht
      · rw [abs_of_neg (by linarith [ht.2] : t < 0)]
        constructor <;> linarith [ht.1,ht.2]
      · rw [abs_of_pos (by linarith [ht.1] : 0 < t)]
        constructor <;> linarith [ht.1,ht.2]
    exact hgap t (lt_of_lt_of_le hε hb.1) hb.2 he
  refine ⟨V,hVo,hV1,?_⟩
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
