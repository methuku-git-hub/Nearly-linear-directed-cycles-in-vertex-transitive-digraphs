import DirectedCycles.FiniteCoverRepresentatives
import DirectedCycles.LocalApproximateSets
import DirectedCycles.LocalConjugateWordDomains
import DirectedCycles.LocalDivision

set_option autoImplicit false
namespace DirectedCycles
variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed finite coordinate cover of A squared constructs an actual
symmetric local covering set. Its size bound is independent of the scale. -/
theorem local_approximate_of_coordinate_cover (L : LocalGroupAlgebra G)
    (hd : L.DivisionClosed) (hr : L.Reversible) (A : Set G)
    (hA1 : L.one ∈ A) (hAi : ∀ a ∈ A, L.inv a ∈ A)
    (hdom : L.AllProductsDefined A 200) (v : G → E) (F : Finset E) {r : ℝ}
    (hcover : ∀ x ∈ L.wordPower A 2, ∃ c ∈ F, ‖v x-r • c‖ < r/16)
    (hclose : ∀ x ∈ L.wordPower A 2, ∀ y ∈ L.wordPower A 2,
      ‖v x-v y‖ < r/8 → ∀ d, L.mulRel (L.inv x) y d → d ∈ A) :
    IsLocalApproximateSet L (2*(F.card+1)) A := by
  classical
  let : Nonempty G := ⟨L.one⟩
  obtain ⟨T,hT,hTcard,hTcover⟩ := finite_cover_representatives F (L.wordPower A 2)
    (fun c x => ‖v x-r • c‖ < r/16) hcover
  let X := T ∪ T.image L.inv
  have hX2 : (X : Set G) ⊆ L.wordPower A 2 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hT hx
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact L.inv_mem_wordPower hr hAi (hT ha)
  refine ⟨by omega,hA1,hAi,hdom,⟨X,?_,?_,?_,?_⟩⟩
  · calc
      X.card ≤ T.card+(T.image L.inv).card := Finset.card_union_le _ _
      _ ≤ T.card+T.card := Nat.add_le_add_left Finset.card_image_le _
      _ ≤ 2*(F.card+1) := by omega
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      rw [L.inv_inv]
      exact Finset.mem_union_left _ ha
  · exact hX2.trans (L.wordPower_subset_wordPower hA1 hdom (by omega) (by omega))
  · intro x hx
    obtain ⟨y,hy,c,_,hcx,hcy⟩ := hTcover x hx
    have hdist : ‖v y-v x‖ < r/8 := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (v y) (r • c) (v x)
      rw [norm_sub_rev (r • c) (v x)] at ht
      linarith
    have hyA := hT hy
    have hyi := L.inv_mem_wordPower hr hAi hyA
    have hdom2 := hdom.wordPower L (by norm_num : 2*2 ≤ 200)
    obtain ⟨d,hpd⟩ := hdom2 [L.inv y,x] (by simp) (by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact hyi
      · exact hx)
    have hm := (LocalGroupAlgebra.Product.pair_iff L _ _ _).1 hpd
    refine ⟨y,Finset.mem_union_left _ hy,d,hclose y hyA x hx hdist d hm,?_⟩
    simpa only [L.inv_inv] using hd.left hm
end DirectedCycles
