module

public import DirectedCycles.LocalTripleProducts
public import DirectedCycles.LocalCurveSmallPreimage
public import DirectedCycles.LocalExponentialWordNeighbourhood
public import DirectedCycles.LocalDivision

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E F : Type*} [TopologicalSpace H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H] [NormedAddCommGroup F]

/-- In actual product coordinates of a local group, the specified bounded
curve-segment equivalence is exactly equality of transverse coordinates on a
constructed open symmetric window. Every auxiliary product is defined. -/
theorem local_curve_slice_relation {Q : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) Q)
    (hd : Q.DivisionClosed) (f : ℝ → H) (hf0 : f 0 = Q.one) (hfc : ContinuousAt f 0)
    (hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hadd : ∀ s t : ℝ, |s|+|t| ≤ 1 → Q.mulRel (f s) (f t) (f (s+t)))
    (hgap : ∀ t : ℝ, 0 < |t| → |t| ≤ 1 → f t ≠ Q.one)
    (a : OpenPartialHomeomorph (ℝ × F) H) (ha0 : (0 : ℝ × F) ∈ a.source) (ha1 : a 0 = Q.one)
    (σ : F → H)
    (hformula : ∀ᶠ p : ℝ × F in 𝓝 0, Q.mulRel (f p.1) (σ p.2) (a p)) :
    ∃ W : Set H, IsOpen W ∧ Q.one ∈ W ∧ (∀ x ∈ W, Q.inv x ∈ W) ∧ W ⊆ a.target ∧
      ∀ x ∈ W, ∀ y ∈ W,
        (∃ p ∈ f '' Set.Icc (-1 : ℝ) 1, Q.mulRel x (Q.inv y) p) ↔
          (a.symm x).2 = (a.symm y).2 := by
  obtain ⟨B,hBo,hB1,_,_,hBdom,_⟩ := D.exists_open_word_neighbourhood Set.univ (Filter.univ_mem) 2
  have hfT : Filter.Tendsto f (𝓝 0) (𝓝 Q.one) := by simpa only [hf0] using hfc.tendsto
  obtain ⟨rf,hrf,hfB⟩ := Metric.mem_nhds_iff.mp (hfT.eventually (hBo.mem_nhds hB1))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (a.open_source.mem_nhds ha0) hformula)
  let δ : ℝ := min r (min rf 1)
  have hδ : 0 < δ := lt_min hr (lt_min hrf (by norm_num))
  have hδr : δ ≤ r := min_le_left _ _
  have hδf : δ ≤ rf := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hfsmall : ∀ t : ℝ, |t| < δ → f t ∈ B := by
    intro t ht
    apply hfB
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht.trans_le hδf
  have hbox : ∀ t : ℝ, ∀ z : F, |t| < δ → ‖z‖ < δ →
      (t,z) ∈ a.source ∧ Q.mulRel (f t) (σ z) (a (t,z)) := by
    intro t z ht hz
    apply hball
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs]
    exact (max_lt ht hz).trans_le hδr
  obtain ⟨U,hUo,hU1,hUsmall⟩ := local_curve_small_preimage f Q.one hcont hgap (show 0 < δ/4 by positivity)
  have htarget : Q.one ∈ a.target := ha1 ▸ a.mapsTo ha0
  have hs1 : a.symm Q.one = 0 := by rw [← ha1]; exact a.left_inv ha0
  let T : Set H := a.target ∩ a.symm ⁻¹' Metric.ball (0 : ℝ × F) (δ/4)
  have hT : T ∈ 𝓝 Q.one := by
    apply Filter.inter_mem (a.open_target.mem_nhds htarget)
    apply (a.continuousAt_symm htarget).preimage_mem_nhds
    rw [hs1]
    exact Metric.ball_mem_nhds _ (by positivity)
  obtain ⟨W,hWo,hW1,hWi,hWsub,_,hWp⟩ := D.exists_open_word_neighbourhood (U ∩ B ∩ T)
    (Filter.inter_mem (Filter.inter_mem (hUo.mem_nhds hU1) (hBo.mem_nhds hB1)) hT) 2
  have hWtarget : W ⊆ a.target := fun _ hx => (hWsub hx).2.1
  have hsmall : ∀ x ∈ W, |(a.symm x).1| < δ/4 ∧ ‖(a.symm x).2‖ < δ/4 := by
    intro x hx
    have hh := (hWsub hx).2.2
    simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using hh
  have hdiff : ∀ x ∈ W, ∀ y ∈ W, ∀ z, Q.mulRel x (Q.inv y) z → z ∈ U := by
    intro x hx y hy z hz
    exact (hWp 2 le_rfl ⟨[x,Q.inv y],rfl,by aesop,(LocalGroupAlgebra.Product.pair_iff Q _ _ _).2 hz⟩).1.1
  refine ⟨W,hWo,hW1,hWi,hWtarget,?_⟩
  intro x hx y hy
  let p := a.symm x
  let q := a.symm y
  have hp := hsmall x hx
  have hq := hsmall y hy
  have hps : p ∈ a.source := a.symm.mapsTo (hWtarget hx)
  have hpx : a p = x := a.right_inv (hWtarget hx)
  have hqy : a q = y := a.right_inv (hWtarget hy)
  have hpf : Q.mulRel (f p.1) (σ p.2) x := by
    have hh := (hbox p.1 p.2 (by dsimp [p]; linarith [hp.1]) (by dsimp [p]; linarith [hp.2])).2
    simpa only [hpx] using hh
  have hqf : Q.mulRel (f q.1) (σ q.2) y := by
    have hh := (hbox q.1 q.2 (by dsimp [q]; linarith [hq.1]) (by dsimp [q]; linarith [hq.2])).2
    simpa only [hqy] using hh
  constructor
  · rintro ⟨_,⟨s,hs,rfl⟩,hm⟩
    have hsδ : |s| < δ/4 := hUsmall s (abs_le.2 hs) (hdiff x hx y hy _ hm)
    have hb := hbox (s+q.1) q.2 (by
      have hh := abs_add_le s q.1
      dsimp [q] at hh
      linarith [hq.1]) (by dsimp [q]; linarith [hq.2])
    have hsy : Q.mulRel (f s) y x := by simpa only [Q.inv_inv] using hd.right hm
    have hsf := hadd s q.1 (by dsimp [q]; linarith [hq.1])
    have he : a (s+q.1,q.2) = x := Q.assoc hsf hqf hb.2 hsy
    have heq : (s+q.1,q.2) = p := a.injOn hb.1 hps (he.trans hpx.symm)
    exact (congrArg (Prod.snd : ℝ × F → F) heq).symm
  · intro heq
    change p.2 = q.2 at heq
    have hsδ : |p.1-q.1| < δ := by
      have hh : |p.1-q.1| ≤ |p.1|+|q.1| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le p.1 (-q.1)
      dsimp [p,q] at hh
      linarith [hp.1,hq.1]
    have hfsB := hfsmall (p.1-q.1) hsδ
    have hyB : y ∈ B := (hWsub hy).1.2
    obtain ⟨z,hz⟩ := hBdom [f (p.1-q.1),y] (by simp) (by aesop)
    have hm : Q.mulRel (f (p.1-q.1)) y z := (LocalGroupAlgebra.Product.pair_iff Q _ _ _).1 hz
    have hsf := hadd (p.1-q.1) q.1 (by
      have hh : |p.1-q.1| ≤ |p.1|+|q.1| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le p.1 (-q.1)
      dsimp [p,q] at hh
      linarith [hp.1,hq.1])
    rw [sub_add_cancel] at hsf
    have hpf' : Q.mulRel (f p.1) (σ q.2) x := heq ▸ hpf
    have hzx : x = z := Q.assoc hsf hqf hpf' hm
    rw [← hzx] at hm
    exact ⟨f (p.1-q.1),⟨p.1-q.1,abs_le.1 (hsδ.le.trans hδ1),rfl⟩,hd.right hm⟩
end DirectedCycles
