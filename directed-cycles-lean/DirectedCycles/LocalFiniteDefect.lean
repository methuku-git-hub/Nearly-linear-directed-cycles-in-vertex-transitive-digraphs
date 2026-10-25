module

public import DirectedCycles.LocalFiniteRightTranslate
public import DirectedCycles.LocalFiniteProductCard

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

theorem rightTranslate_sdiff [DecidableEq G] (hc : L.Cancellative) (B C : Finset G) (g : G) :
    L.rightTranslate (B\C) g = L.rightTranslate B g\L.rightTranslate C g := by
  classical
  ext x
  simp only [L.mem_rightTranslate,Finset.mem_sdiff]
  constructor
  · rintro ⟨b,⟨hb,hbC⟩,hm⟩
    refine ⟨⟨b,hb,hm⟩,?_⟩
    rintro ⟨c,hcC,hcm⟩
    exact hbC ((hc.right_cancel hm hcm).symm ▸ hcC)
  · rintro ⟨⟨b,hb,hm⟩,hxC⟩
    exact ⟨b,⟨hb,fun hbC => hxC ⟨b,hbC,hm⟩⟩,hm⟩

theorem card_rightTranslate_le (B : Finset G) (g : G) : (L.rightTranslate B g).card ≤ B.card := by
  classical
  have hh := L.card_setMul_le B {g}
  rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card'] at hh
  simpa only [rightTranslate,finsetMul,Finset.card_singleton,Nat.mul_one] using hh

noncomputable def defect (B : Finset G) (g : G) : ℕ := by
  classical
  exact (B\L.rightTranslate B g).card

theorem defect_one (B : Finset G) : L.defect B L.one = 0 := by
  classical
  simp only [defect,L.rightTranslate_one,Finset.sdiff_self,Finset.card_empty]

theorem defect_add_overlap [DecidableEq G] (B : Finset G) (g : G) :
    L.defect B g+(B ∩ L.rightTranslate B g).card = B.card := by
  classical
  convert Finset.card_sdiff_add_card_inter B (L.rightTranslate B g) using 2
  unfold defect
  congr 1
  ext x
  simp only [Finset.mem_sdiff]

/-- Defect subadditivity uses composition only inside a certified local
domain. The last cardinal estimate merely uses contraction of a partial
translation, so it introduces no global action assumption. -/
theorem defect_mul_le (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) (B : Finset G) (hBR : (B : Set G) ⊆ R)
    {g h gh : G} (hg : g ∈ R) (hh : h ∈ R) (hgh : L.mulRel g h gh) :
    L.defect B gh ≤ L.defect B g+L.defect B h := by
  classical
  have he := L.rightTranslate_mul hdom B hBR hg hh hgh
  have hs : B\L.rightTranslate B gh ⊆
      (B\L.rightTranslate B h) ∪ (L.rightTranslate B h\L.rightTranslate (L.rightTranslate B g) h) := by
    intro x hx
    obtain ⟨hxB,hxn⟩ := Finset.mem_sdiff.mp hx
    rw [← he] at hxn
    by_cases hx' : x ∈ L.rightTranslate B h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx',hxn⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxB,hx'⟩)
  calc
    L.defect B gh ≤ ((B\L.rightTranslate B h) ∪
        (L.rightTranslate B h\L.rightTranslate (L.rightTranslate B g) h)).card := Finset.card_le_card hs
    _ ≤ (B\L.rightTranslate B h).card+
        (L.rightTranslate B h\L.rightTranslate (L.rightTranslate B g) h).card := Finset.card_union_le _ _
    _ = L.defect B h+(L.rightTranslate (B\L.rightTranslate B g) h).card := by
      rw [L.rightTranslate_sdiff hc]
      rfl
    _ ≤ L.defect B h+L.defect B g := Nat.add_le_add_left (L.card_rightTranslate_le _ h) _
    _ = L.defect B g+L.defect B h := Nat.add_comm _ _

theorem defect_inv (hd : L.DivisionClosed) (hr : L.Reversible) (B : Finset G) (g : G)
    (hg : ∀ b ∈ B, L.Defined b g) (hgi : ∀ b ∈ B, L.Defined b (L.inv g)) :
    L.defect B (L.inv g) = L.defect B g := by
  classical
  have hc := hd.cancellative L hr
  have hcancel : L.rightTranslate (L.rightTranslate B (L.inv g)) g = B := by
    simpa only [L.inv_inv] using L.rightTranslate_inv hd B (L.inv g) hgi
  have he : (B ∩ L.rightTranslate B (L.inv g)).card = (B ∩ L.rightTranslate B g).card := by
    rw [← L.card_rightTranslate hc (B ∩ L.rightTranslate B (L.inv g)) g
      (fun b hb => hg b (Finset.mem_inter.mp hb).1),L.rightTranslate_inter hc,hcancel,Finset.inter_comm]
  have h1 := L.defect_add_overlap B (L.inv g)
  have h2 := L.defect_add_overlap B g
  omega

/-- Small defect gives an actual difference factorization by local division. -/
theorem mem_difference_of_defect_lt (hd : L.DivisionClosed) (B : Finset G) (g : G)
    (h : L.defect B g < B.card) : g ∈ L.setMul (L.inv '' (B : Set G)) (B : Set G) := by
  classical
  have ho : 0 < (B ∩ L.rightTranslate B g).card := by
    have hh := L.defect_add_overlap B g
    omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp ho
  obtain ⟨hxB,hxg⟩ := Finset.mem_inter.mp hx
  obtain ⟨b,hb,hbg⟩ := (L.mem_rightTranslate B g x).1 hxg
  exact ⟨L.inv b,⟨b,hb,rfl⟩,x,hxB,hd.left hbg⟩
end LocalGroupAlgebra
end DirectedCycles
