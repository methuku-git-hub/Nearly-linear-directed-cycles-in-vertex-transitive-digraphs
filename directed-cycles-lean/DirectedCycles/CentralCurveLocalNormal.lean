import DirectedCycles.OneParameterKernelGap
import DirectedCycles.LocalQuotientSeparation

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]

/-- A central continuous curve with no short period gives an actual compact
locally normal segment on an open identity neighbourhood. The neighbourhood
is constructed by excluding the compact image of the parameter annulus. -/
theorem central_curve_locally_normal (φ : ℝ → H) (hcont : Continuous φ) (h0 : φ 0 = 1)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hcentral : ∀ t : ℝ, ∀ x : H, Commute (φ t) x)
    {R : ℝ} (hR : 0 < R)
    (hgap : ∀ t : ℝ, 0 < |t| → |t| ≤ 2*R → φ t ≠ 1) :
    ∃ V : Set H, IsOpen V ∧ (1 : H) ∈ V ∧
      LocalNormalSet (φ '' Set.Icc (-R) R) V ∧ IsCompact (φ '' Set.Icc (-R) R) := by
  let B : Set ℝ := Set.Icc (-2*R) (-R) ∪ Set.Icc R (2*R)
  let V := (φ '' B)ᶜ
  have hBc : IsCompact B := isCompact_Icc.union isCompact_Icc
  have hVo : IsOpen V := (hBc.image hcont).isClosed.isOpen_compl
  have hV1 : (1 : H) ∈ V := by
    rintro ⟨t,ht,he⟩
    have hb : R ≤ |t| ∧ |t| ≤ 2*R := by
      rcases ht with ht | ht
      · rw [abs_of_neg (by linarith [ht.2] : t < 0)]
        constructor <;> linarith [ht.1,ht.2]
      · rw [abs_of_pos (by linarith [ht.1] : 0 < t)]
        constructor <;> linarith [ht.1,ht.2]
    exact hgap t (lt_of_lt_of_le hR hb.1) hb.2 he
  refine ⟨V,hVo,hV1,?_,isCompact_Icc.image hcont⟩
  constructor
  · exact ⟨0,⟨by linarith,by linarith⟩,h0⟩
  · rintro x ⟨s,hs,rfl⟩
    refine ⟨-s,⟨by linarith [hs.2],by linarith [hs.1]⟩,?_⟩
    exact real_curve_neg φ h0 hadd s
  · rintro x ⟨s,hs,rfl⟩ y ⟨t,ht,rfl⟩ hprod
    have hsum : s+t ∈ Set.Icc (-R) R := by
      by_contra hn
      have hb : s+t ∈ B := by
        have hsumlo : -2*R ≤ s+t := by linarith [hs.1,ht.1]
        have hsumhi : s+t ≤ 2*R := by linarith [hs.2,ht.2]
        by_cases hh : s+t < -R
        · exact Or.inl ⟨hsumlo,hh.le⟩
        · right
          exact ⟨by have : ¬ s+t ≤ R := fun h => hn ⟨by linarith,h⟩; linarith,hsumhi⟩
      exact hprod ⟨s+t,hb,hadd s t⟩
    exact ⟨s+t,hsum,hadd s t⟩
  · rintro x _ p ⟨t,ht,rfl⟩ _
    refine ⟨t,ht,?_⟩
    have hc := (hcentral t x).eq
    calc
      φ t = φ t*(x*x⁻¹) := by rw [mul_inv_cancel,mul_one]
      _ = (x*φ t)*x⁻¹ := by rw [← mul_assoc,hc]

/-- The no-short-period hypothesis above follows from the actual NSS model
region and nontriviality, with no Lie-algebra assertion added. -/
theorem central_nss_curve_locally_normal (φ : ℝ → H) (hcont : Continuous φ) (h0 : φ 0 = 1)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t) (h1 : φ 1 ≠ 1)
    (hcentral : ∀ t : ℝ, ∀ x : H, Commute (φ t) x)
    (T : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ T) → x = 1)
    {R : ℝ} (hR : 0 < R) (hbound : ∀ t : ℝ, |t| ≤ R → φ t ∈ T) :
    ∃ V : Set H, IsOpen V ∧ (1 : H) ∈ V ∧
      LocalNormalSet (φ '' Set.Icc (-R) R) V ∧ IsCompact (φ '' Set.Icc (-R) R) :=
  central_curve_locally_normal φ hcont h0 hadd hcentral hR
    (fun _ ht hb => real_curve_kernel_gap φ h0 hadd h1 T hNSS R hbound ht hb)
end DirectedCycles
