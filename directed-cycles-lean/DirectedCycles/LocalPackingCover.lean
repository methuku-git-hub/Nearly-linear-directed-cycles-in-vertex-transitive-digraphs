import DirectedCycles.FiniteFamilyPacking
import DirectedCycles.LocalFiniteLeftTranslate
import DirectedCycles.LocalWordPowerIteration
import DirectedCycles.LocalWordPowerMonotonicity

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- Maximal disjoint local translates give a cover of S^4 by translates of
S^2. Reassociation occurs only inside the proved twelve-letter S-domain. -/
theorem packing_power_cover (hd : L.DivisionClosed) (hr : L.Reversible)
    (S : Finset G) (h1 : L.one ∈ S) (hi : ∀ s ∈ S, L.inv s ∈ S)
    {N : ℕ} (hdom : L.AllProductsDefined (S : Set G) N) (hN : 12 ≤ N) :
    ∃ X : Finset G, (X : Set G) ⊆ L.wordPower (S : Set G) 4 ∧
      X.card*S.card ≤ Nat.card (L.wordPower (S : Set G) 5) ∧
      L.wordPower (S : Set G) 4 ⊆ L.setMul (X : Set G) (L.wordPower (S : Set G) 2) := by
  classical
  let I := (L.wordPower (S : Set G) 4).toFinset
  let R := (L.wordPower (S : Set G) 5).toFinset
  have hc := hd.cancellative L hr
  have hS4 : (S : Set G) ⊆ L.wordPower (S : Set G) 4 := by
    simpa only [L.wordPower_one] using L.wordPower_subset_wordPower h1 hdom (by omega : 1 ≤ 4) (by omega)
  have h4dom : L.AllProductsDefined (L.wordPower (S : Set G) 4) 3 := hdom.wordPower L (by omega)
  have hTR : ∀ a ∈ I, L.leftTranslate S a ⊆ R := by
    intro a ha z hz
    obtain ⟨s,hs,hm⟩ := (L.mem_leftTranslate S a z).1 hz
    apply Set.mem_toFinset.mpr
    rw [show 5 = 4+1 from rfl,L.wordPower_add hdom (by omega),L.wordPower_one]
    exact ⟨a,Set.mem_toFinset.mp ha,s,hs,hm⟩
  have hsize : ∀ a ∈ I, (L.leftTranslate S a).card = S.card := by
    intro a ha
    apply L.card_leftTranslate hc
    intro s hs
    obtain ⟨x,hx⟩ := h4dom [a,s] (by simp) (by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl
      · exact Set.mem_toFinset.mp ha
      · exact hS4 hs)
    exact ⟨x,(Product.pair_iff L _ _ _).1 hx⟩
  obtain ⟨X,hXI,hcard,hoverlap⟩ := FiniteAlmostPeriods.finite_family_packing I R (L.leftTranslate S)
    S.card (Finset.card_pos.mpr ⟨L.one,h1⟩) hTR hsize
  refine ⟨X,(fun x hx => Set.mem_toFinset.mp (hXI hx)),?_,?_⟩
  · rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
    exact hcard
  · intro z hz
    obtain ⟨x,hx,p,hp⟩ := hoverlap z (Set.mem_toFinset.mpr hz)
    obtain ⟨hpz,hpx⟩ := Finset.mem_inter.mp hp
    obtain ⟨s,hs,hzs⟩ := (L.mem_leftTranslate S z p).1 hpz
    obtain ⟨t,ht,hxt⟩ := (L.mem_leftTranslate S x p).1 hpx
    have his := hi s hs
    obtain ⟨v,hv⟩ := hdom [t,L.inv s] (by simp; omega) (by aesop)
    have htv := (Product.pair_iff L _ _ _).1 hv
    have hv2 : v ∈ L.wordPower (S : Set G) 2 := ⟨[t,L.inv s],rfl,by aesop,hv⟩
    obtain ⟨w,hw,hxv⟩ := h4dom.triple L (Set.mem_toFinset.mp (hXI hx)) (hS4 ht) (hS4 his) hxt htv
    have he : w = z := L.unique hw (hd.right hzs)
    exact ⟨x,hx,v,hv2,he ▸ hxv⟩

/-- A local square is an approximate group once the preceding packing bound
is small. Its 200-letter domain is derived from the actual 400-letter
S-domain, and the cover is symmetrized explicitly. -/
theorem square_approximate_of_packing (hd : L.DivisionClosed) (hr : L.Reversible)
    (S : Finset G) (h1 : L.one ∈ S) (hi : ∀ s ∈ S, L.inv s ∈ S)
    {N J : ℕ} (hdom : L.AllProductsDefined (S : Set G) N) (hN : 400 ≤ N)
    (hJ : 1 ≤ J) (hcard : Nat.card (L.wordPower (S : Set G) 5) ≤ J*S.card) :
    IsLocalFiniteApproximateGroup L (2*J) (by classical exact (L.wordPower (S : Set G) 2).toFinset) := by
  classical
  let B := (L.wordPower (S : Set G) 2).toFinset
  have hBcoe : (B : Set G) = L.wordPower (S : Set G) 2 := Set.coe_toFinset _
  have hB1 : L.one ∈ B := Set.mem_toFinset.mpr
    (L.wordPower_subset_wordPower h1 hdom (by omega : 1 ≤ 2) (by omega)
      (by rw [L.wordPower_one]; exact h1))
  have hBdom : L.AllProductsDefined (B : Set G) 200 := by
    rw [hBcoe]
    exact hdom.wordPower L (by omega)
  have hS4B2 : L.wordPower (S : Set G) 4 = L.wordPower (B : Set G) 2 := by
    rw [show 4 = 2+2 from rfl,L.wordPower_add hdom (by omega),
      show 2 = 1+1 from rfl,L.wordPower_add hBdom (by norm_num),L.wordPower_one,hBcoe]
  obtain ⟨X,hX4,hXcard,hcover⟩ := L.packing_power_cover hd hr S h1 hi hdom (by omega)
  have hXJ : X.card ≤ J := by
    have hSc : 0 < S.card := Finset.card_pos.mpr ⟨L.one,h1⟩
    exact Nat.le_of_mul_le_mul_right (hXcard.trans hcard) hSc
  let Y := X ∪ X.image L.inv
  have hY4 : (Y : Set G) ⊆ L.wordPower (S : Set G) 4 := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hX4 hy
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact L.inv_mem_wordPower hr hi (hX4 hx)
  refine ⟨by omega,hB1,?_,hBdom,⟨Y,?_,?_,?_,?_⟩⟩
  · intro b hb
    exact Set.mem_toFinset.mpr (L.inv_mem_wordPower hr hi (Set.mem_toFinset.mp hb))
  · calc
      Y.card ≤ X.card+(X.image L.inv).card := Finset.card_union_le _ _
      _ ≤ X.card+X.card := Nat.add_le_add_left Finset.card_image_le _
      _ ≤ 2*J := by omega
  · intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      rw [L.inv_inv]
      exact Finset.mem_union_left _ hx
  · exact hY4.trans (hS4B2 ▸ L.wordPower_subset_wordPower hB1 hBdom (by norm_num : 2 ≤ 3) (by norm_num))
  · intro z hz
    obtain ⟨x,hx,b,hb,hm⟩ := hcover (hS4B2.symm ▸ hz)
    exact ⟨x,Finset.mem_union_left _ hx,b,Set.mem_toFinset.mpr hb,hm⟩
end LocalGroupAlgebra
end DirectedCycles
