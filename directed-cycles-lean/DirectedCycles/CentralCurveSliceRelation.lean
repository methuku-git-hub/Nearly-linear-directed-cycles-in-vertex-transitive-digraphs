module

public import DirectedCycles.OneParameterSmallPreimage
public import DirectedCycles.OpenSymmetricQuotientWindow

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {H F : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup F]

/-- In genuine product coordinates along a central curve, the actual bounded
central-segment equivalence is precisely equality of transverse coordinates on
a sufficiently small open symmetric group neighbourhood. -/
theorem central_curve_slice_relation (φ : ℝ → H) (hcont : Continuous φ)
    (hadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hcentral : ∀ t : ℝ, ∀ x : H, Commute (φ t) x)
    {R : ℝ} (hR : 0 < R) (hgap : ∀ t : ℝ, 0 < |t| → |t| ≤ R → φ t ≠ 1)
    (a : OpenPartialHomeomorph (ℝ × F) H) (ha0 : (0 : ℝ × F) ∈ a.source) (ha1 : a 0 = 1)
    (σ : F → H) (hformula : ∀ᶠ p : ℝ × F in 𝓝 (0 : ℝ × F), a p = φ p.1*σ p.2) :
    ∃ W : Set H, IsOpen W ∧ (1 : H) ∈ W ∧ W⁻¹ = W ∧ W ⊆ a.target ∧
      ∀ x ∈ W, ∀ y ∈ W,
        x⁻¹*y ∈ φ '' Set.Icc (-R) R ↔ (a.symm x).2 = (a.symm y).2 := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (a.open_source.mem_nhds ha0) hformula)
  let δ := min r R
  have hδ : 0 < δ := lt_min hr hR
  have hδR : δ ≤ R := min_le_right _ _
  have hbox : ∀ t : ℝ, ∀ z : F, |t| < δ → ‖z‖ < δ →
      (t,z) ∈ a.source ∧ a (t,z) = φ t*σ z := by
    intro t z ht hz
    apply hball
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs]
    exact (max_lt ht hz).trans_le (min_le_left _ _)
  obtain ⟨U,hUo,hU1,hUsmall⟩ := one_parameter_small_preimage φ hcont (show 0 < δ/4 by positivity) hgap
  have h1target : (1 : H) ∈ a.target := ha1 ▸ a.mapsTo ha0
  have hs1 : a.symm 1 = 0 := by rw [← ha1]; exact a.left_inv ha0
  let T : Set H := a.target ∩ a.symm ⁻¹' Metric.ball (0 : ℝ × F) (δ/4)
  have hT : T ∈ 𝓝 (1 : H) := by
    apply Filter.inter_mem (a.open_target.mem_nhds h1target)
    apply (a.continuousAt_symm h1target).preimage_mem_nhds
    rw [hs1]
    exact Metric.ball_mem_nhds _ (by positivity)
  obtain ⟨W,hWo,hW1,hWi,hW6⟩ := exists_open_symmetric_sixth_subset
    (Filter.inter_mem (hUo.mem_nhds hU1) hT)
  have hWT : W ⊆ U ∩ T := by
    have hh := (Set.pow_subset_pow_right hW1 (by omega : 1 ≤ 6)).trans hW6
    simpa only [pow_one] using hh
  have hWtarget : W ⊆ a.target := fun x hx => (hWT hx).2.1
  have hsmall : ∀ x ∈ W, |(a.symm x).1| < δ/4 ∧ ‖(a.symm x).2‖ < δ/4 := by
    intro x hx
    have hb := (hWT hx).2.2
    change a.symm x ∈ Metric.ball (0 : ℝ × F) (δ/4) at hb
    simpa only [Metric.mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using hb
  have hdiff : ∀ x ∈ W, ∀ y ∈ W, x⁻¹*y ∈ U := by
    intro x hx y hy
    have hxi : x⁻¹ ∈ W := by rw [← hWi]; simpa only [Set.mem_inv,inv_inv] using hx
    have hp : x⁻¹*y ∈ W^2 := by rw [pow_two]; exact Set.mul_mem_mul hxi hy
    exact (hW6 ((Set.pow_subset_pow_right hW1 (by omega : 2 ≤ 6)) hp)).1
  refine ⟨W,hWo,hW1,hWi,hWtarget,?_⟩
  intro x hx y hy
  let p := a.symm x
  let q := a.symm y
  have hp := hsmall x hx
  have hq := hsmall y hy
  have hqs : q ∈ a.source := a.symm.mapsTo (hWtarget hy)
  have hpx : a p = x := a.right_inv (hWtarget hx)
  have hqy : a q = y := a.right_inv (hWtarget hy)
  have hpf : x = φ p.1*σ p.2 := hpx.symm.trans (hbox p.1 p.2 (by dsimp [p]; linarith [hp.1]) (by dsimp [p]; linarith [hp.2])).2
  have hqf : y = φ q.1*σ q.2 := hqy.symm.trans (hbox q.1 q.2 (by dsimp [q]; linarith [hq.1]) (by dsimp [q]; linarith [hq.2])).2
  constructor
  · rintro ⟨s,hs,he⟩
    have hsR : |s| ≤ R := abs_le.2 hs
    have hsδ : |s| < δ/4 := hUsmall s hsR (he.symm ▸ hdiff x hx y hy)
    have hsp : |s+p.1| < δ := by
      have hh := abs_add_le s p.1
      dsimp [p] at hh
      linarith [hp.1]
    have hb := hbox (s+p.1) p.2 hsp (by dsimp [p]; linarith [hp.2])
    have hys : y = φ s*x := by
      calc
        y = x*(x⁻¹*y) := (mul_inv_cancel_left x y).symm
        _ = x*φ s := by rw [he]
        _ = φ s*x := (hcentral s x).eq.symm
    have hae : a (s+p.1,p.2) = y := by
      rw [hb.2,hadd,mul_assoc,← hpf,← hys]
    have heq : (s+p.1,p.2) = q := a.injOn hb.1 hqs (hae.trans hqy.symm)
    have hh := congrArg (Prod.snd : ℝ × F → F) heq
    exact hh
  · intro heq
    change p.2 = q.2 at heq
    have hsR : |q.1-p.1| ≤ R := by
      have hsub : |q.1-p.1| ≤ |q.1|+|p.1| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le q.1 (-p.1)
      dsimp [p,q] at hsub
      linarith [hp.1,hq.1]
    refine ⟨q.1-p.1,abs_le.1 hsR,?_⟩
    have hys : φ (q.1-p.1)*x = y := by
      rw [hpf,← mul_assoc,← hadd,sub_add_cancel,heq,← hqf]
    calc
      φ (q.1-p.1) = x⁻¹*(x*φ (q.1-p.1)) := (inv_mul_cancel_left x _).symm
      _ = x⁻¹*(φ (q.1-p.1)*x) := by rw [(hcentral (q.1-p.1) x).eq]
      _ = x⁻¹*y := by rw [hys]
end DirectedCycles
