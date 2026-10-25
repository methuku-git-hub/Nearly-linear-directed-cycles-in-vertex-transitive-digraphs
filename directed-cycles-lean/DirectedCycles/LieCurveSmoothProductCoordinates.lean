module

public import DirectedCycles.LieCurveProductSmoothDomain
public import DirectedCycles.SmoothInverseNeighbourhood

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open IsManifold
namespace DirectedCycles
variable {G E F : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The actual curve product admits coordinates smooth on their whole open
source, with inverse smooth on the whole open target. -/
theorem lie_curve_smooth_product_coordinates (φ : ℝ → G) (hφ0 : φ 0 = 1)
    (hφ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ φ)
    {v : E} (hv : HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0)
    (A : (ℝ × F) ≃L[ℝ] E) (hA : ∀ t : ℝ, A (t,0) = t • v) :
    ∃ a : OpenPartialHomeomorph (ℝ × F) G,
      (0 : ℝ × F) ∈ a.source ∧ a 0 = 1 ∧
      ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source ∧
      ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target ∧
      ∀ᶠ p : ℝ × F in 𝓝 (0 : ℝ × F),
        a p = φ p.1*(chartAt E (1 : G)).symm (A (0,p.2)+(chartAt E (1 : G)) 1) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let e := chartAt E (1 : G)
  let c := e 1
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : c ∈ e.target := e.mapsTo h1
  have he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ G := chart_mem_maximalAtlas (1 : G)
  let z : ℝ × F → E := fun p => A (0,p.2)+c
  let w : ℝ × F → G := fun p => φ p.1*e.symm (z p)
  let g : ℝ × F → E := fun p => e (w p)-c
  have hA0 : A (0,0) = 0 := A.map_zero
  have hz0 : z 0 = c := by simp only [z,Prod.snd_zero,hA0,zero_add]
  have hw0 : w 0 = 1 := by
    dsimp only [w]
    rw [Prod.fst_zero,hφ0,one_mul,hz0]
    exact e.left_inv h1
  have hg0 : g 0 = 0 := by dsimp only [g]; rw [hw0]; exact sub_self _
  obtain ⟨S,hSo,hS0,hgS,hgD⟩ := lie_curve_product_smooth_domain φ hφ0 hφ hv A hA
  obtain ⟨b,hb,hb0,_,hbSmooth,hbInv⟩ := exists_smooth_inverse_neighbourhood g hSo hS0 hgS A hgD
  have hbzero : b 0 = 0 := by rw [hb]; exact hg0
  let a := (b.trans (Homeomorph.addRight c).toOpenPartialHomeomorph).trans e.symm
  have ha0 : (0 : ℝ × F) ∈ a.source := by
    change ((0 : ℝ × F) ∈ b.source ∧ b 0 ∈ Set.univ) ∧ b 0+c ∈ e.target
    exact ⟨⟨hb0,Set.mem_univ _⟩,by rw [hbzero,zero_add]; exact hc⟩
  have ha1 : a 0 = 1 := by
    change e.symm (b 0+c) = 1
    rw [hbzero,zero_add]
    exact e.left_inv h1
  have haInv : (a.symm : G → ℝ × F) = fun x => b.symm (e x-c) := by
    funext x
    change b.symm ((Homeomorph.addRight c).symm (e x)) = b.symm (e x-c)
    rw [Homeomorph.addRight_symm]
    simp only [Homeomorph.coe_addRight,sub_eq_add_neg]
  refine ⟨a,ha0,ha1,?_,?_,?_⟩
  · intro p hp
    change (p ∈ b.source ∧ b p ∈ Set.univ) ∧ b p+c ∈ e.target at hp
    have hbAt : ContDiffAt ℝ ∞ b p := hbSmooth.contDiffAt (b.open_source.mem_nhds hp.1.1)
    have hzAt : ContMDiffAt 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ (fun p => b p+c) p :=
      (hbAt.add contDiffAt_const).contMDiffAt
    have hInv : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm (b p+c) :=
      contMDiffAt_symm_of_mem_maximalAtlas he hp.2
    exact (hInv.comp p hzAt).contMDiffWithinAt
  · intro x hx
    change x ∈ e.source ∧ e x ∈ Set.univ ∩ (Homeomorph.addRight c).symm ⁻¹' b.target at hx
    have hbt : e x-c ∈ b.target := by
      have hh := hx.2.2
      simpa only [Set.mem_preimage,Homeomorph.addRight_symm,Homeomorph.coe_addRight,sub_eq_add_neg] using hh
    have hbAt : ContDiffAt ℝ ∞ b.symm (e x-c) := hbInv.contDiffAt (b.open_target.mem_nhds hbt)
    have heAt : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e x :=
      contMDiffAt_of_mem_maximalAtlas he hx.1
    have hzAt : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x => e x-c) x :=
      heAt.sub contMDiffAt_const
    rw [haInv]
    exact (hbAt.contMDiffAt.comp x hzAt).contMDiffWithinAt
  · have hzCont : Continuous z := (A.continuous.comp (continuous_const.prodMk continuous_snd)).add continuous_const
    have hInvCont : ContinuousAt e.symm (z 0) := by rw [hz0]; exact e.continuousAt_symm hc
    have hwCont : ContinuousAt w 0 :=
      (hφ.continuous.comp continuous_fst).continuousAt.mul (hInvCont.comp hzCont.continuousAt)
    have hnear : ∀ᶠ p : ℝ × F in 𝓝 (0 : ℝ × F), w p ∈ e.source :=
      hwCont.preimage_mem_nhds (by rw [hw0]; exact e.open_source.mem_nhds h1)
    filter_upwards [hnear] with p hp
    change e.symm (b p+c) = w p
    rw [hb]
    change e.symm ((e (w p)-c)+c) = w p
    rw [sub_add_cancel]
    exact e.left_inv hp
end DirectedCycles
