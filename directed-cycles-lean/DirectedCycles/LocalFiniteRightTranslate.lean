module

public import DirectedCycles.LocalDivision
public import DirectedCycles.LocalTripleProducts
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- Finite multiplication keeps only actually defined products. -/
noncomputable def finsetMul (A B : Finset G) : Finset G := by
  classical
  exact (L.setMul (A : Set G) (B : Set G)).toFinset

noncomputable def rightTranslate (B : Finset G) (g : G) : Finset G := by
  classical
  exact L.finsetMul B {g}

theorem mem_rightTranslate (B : Finset G) (g x : G) :
    x ∈ L.rightTranslate B g ↔ ∃ b ∈ B, L.mulRel b g x := by
  classical
  unfold rightTranslate finsetMul
  rw [Set.mem_toFinset,Finset.coe_singleton]
  constructor
  · rintro ⟨b,hb,g',hg,hm⟩
    have he : g' = g := hg
    exact ⟨b,hb,he ▸ hm⟩
  · rintro ⟨b,hb,hm⟩
    exact ⟨b,hb,g,rfl,hm⟩

theorem rightTranslate_one (B : Finset G) : L.rightTranslate B L.one = B := by
  ext x
  rw [L.mem_rightTranslate]
  constructor
  · rintro ⟨b,hb,hm⟩
    exact (L.unique hm (L.mul_one b)).symm ▸ hb
  · exact fun hx => ⟨x,hx,L.mul_one x⟩

theorem card_rightTranslate (hc : L.Cancellative) (B : Finset G) (g : G)
    (hdom : ∀ b ∈ B, L.Defined b g) : (L.rightTranslate B g).card = B.card := by
  classical
  symm
  apply Finset.card_bij (fun b hb => L.mul b g (hdom b hb))
  · intro b hb
    exact (L.mem_rightTranslate B g _).2 ⟨b,hb,L.mul_spec _ _ _⟩
  · intro a ha b hb he
    have hm := L.mul_spec a g (hdom a ha)
    rw [he] at hm
    exact hc.right_cancel hm (L.mul_spec b g (hdom b hb))
  · intro x hx
    obtain ⟨b,hb,hm⟩ := (L.mem_rightTranslate B g x).1 hx
    exact ⟨b,hb,L.unique (L.mul_spec _ _ _) hm⟩

theorem rightTranslate_inv (hd : L.DivisionClosed) (B : Finset G) (g : G)
    (hdom : ∀ b ∈ B, L.Defined b g) :
    L.rightTranslate (L.rightTranslate B g) (L.inv g) = B := by
  ext x
  rw [L.mem_rightTranslate]
  constructor
  · rintro ⟨y,hy,hm⟩
    obtain ⟨b,hb,hbg⟩ := (L.mem_rightTranslate B g y).1 hy
    exact (L.unique hm (hd.right hbg)).symm ▸ hb
  · intro hx
    obtain ⟨y,hy⟩ := hdom x hx
    exact ⟨y,(L.mem_rightTranslate B g y).2 ⟨x,hx,hy⟩,hd.right hy⟩

theorem rightTranslate_inter [DecidableEq G] (hc : L.Cancellative) (B C : Finset G) (g : G) :
    L.rightTranslate (B ∩ C) g = L.rightTranslate B g ∩ L.rightTranslate C g := by
  classical
  ext x
  simp only [L.mem_rightTranslate,Finset.mem_inter]
  constructor
  · rintro ⟨b,⟨hb,hcB⟩,hm⟩
    exact ⟨⟨b,hb,hm⟩,⟨b,hcB,hm⟩⟩
  · rintro ⟨⟨b,hb,hbm⟩,⟨c,hcC,hcm⟩⟩
    have he : b = c := hc.right_cancel hbm hcm
    exact ⟨b,⟨hb,he.symm ▸ hcC⟩,hbm⟩

/-- Right translations compose only on the certified domain. -/
theorem rightTranslate_mul {R : Set G} (hdom : L.AllProductsDefined R 3)
    (B : Finset G) (hBR : (B : Set G) ⊆ R) {g h gh : G}
    (hg : g ∈ R) (hh : h ∈ R) (hgh : L.mulRel g h gh) :
    L.rightTranslate (L.rightTranslate B g) h = L.rightTranslate B gh := by
  ext x
  rw [L.mem_rightTranslate,L.mem_rightTranslate]
  constructor
  · rintro ⟨y,hy,hm⟩
    obtain ⟨b,hb,hbg⟩ := (L.mem_rightTranslate B g y).1 hy
    obtain ⟨z,hz,hbz⟩ := hdom.triple L (hBR hb) hg hh hbg hgh
    have he : z = x := L.unique hz hm
    exact ⟨b,hb,he ▸ hbz⟩
  · rintro ⟨b,hb,hbgh⟩
    obtain ⟨y,hy⟩ := hdom [b,g] (by simp) (by aesop)
    have hbg := (Product.pair_iff L _ _ _).1 hy
    obtain ⟨z,hyh,hbz⟩ := hdom.triple L (hBR hb) hg hh hbg hgh
    have he : z = x := L.unique hbz hbgh
    exact ⟨y,(L.mem_rightTranslate B g y).2 ⟨b,hb,hbg⟩,he ▸ hyh⟩
end LocalGroupAlgebra
end DirectedCycles
