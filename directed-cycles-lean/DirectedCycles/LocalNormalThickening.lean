module

public import DirectedCycles.LocalNormalSubgroupQuotient
public import DirectedCycles.LocalSubgroupAction
public import DirectedCycles.LocalTripleProducts
public import DirectedCycles.LocalProductCompression

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} {L : LocalGroupAlgebra G} {H A B : Set G}

/-- Normalizing a generating neighbourhood extends to its H-thickening. The
four-letter domain supplies every intermediate product, and H absorbs all
extra subgroup factors. -/
theorem IsGlobalSubgroup.normalThickening (hH : L.IsGlobalSubgroup H)
    (hr : L.Reversible) (hHA : H ⊆ A) (hBA : B ⊆ A) (hB1 : L.one ∈ B)
    (hBi : ∀ b ∈ B, L.inv b ∈ B) (hdom : L.AllProductsDefined A 4)
    (hnorm : ∀ b ∈ B, ∀ h ∈ H, ∃ k ∈ H, ∃ t, L.mulRel b h t ∧ L.mulRel k b t) :
    L.NormalSubgroupWindow H (L.setMul H B) := by
  have hdom3 := hdom.mono L (Set.Subset.refl A) (by omega : 3 ≤ 4)
  have hbinary : ∀ a ∈ L.setMul H B, ∀ b ∈ L.setMul H B, L.Defined a b := by
    intro a ha b hb
    obtain ⟨h,hh,x,hx,hha⟩ := ha
    obtain ⟨k,hk,y,hy,hkb⟩ := hb
    obtain ⟨z,hz⟩ := hdom [h,x,k,y] (by simp) (by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hHA hh
      · exact hBA hx
      · exact hHA hk
      · exact hBA hy)
    have hblocks : List.Forall₂ L.Product [[h,x],[k,y]] [a,b] :=
      List.Forall₂.cons ((Product.pair_iff L h x a).2 hha)
        (List.Forall₂.cons ((Product.pair_iff L k y b).2 hkb) List.Forall₂.nil)
    have hpair : L.Product [a,b] z := (show L.Product ([[h,x],[k,y]] : List (List G)).flatten z from hz).compress L hblocks
    exact ⟨z,(Product.pair_iff L a b z).1 hpair⟩
  refine ⟨hH,?_,?_,hbinary,?_,?_⟩
  · intro h hh
    exact ⟨h,hh,L.one,hB1,L.mul_one h⟩
  · intro s hs
    obtain ⟨h,hh,b,hb,hm⟩ := hs
    obtain ⟨k,hk,t,ht,ht'⟩ := hnorm (L.inv b) (hBi b hb) (L.inv h) (hH.inv_mem h hh)
    have he : t = L.inv s := L.unique ht (hr hm)
    exact ⟨k,hk,L.inv b,hBi b hb,he ▸ ht'⟩
  · intro h hh s hs
    exact hH.mul_thickening hHA hBA hdom3 hh hs
  · intro s hs k hk
    obtain ⟨h,hh,b,hb,hhs⟩ := hs
    obtain ⟨l,hl,t,hbk,hlb⟩ := hnorm b hb k hk
    let := hH.toGroup
    let h' : H := ⟨h,hh⟩
    let l' : H := ⟨l,hl⟩
    let r : H := h'*l'
    let q : H := h'*l'*h'⁻¹
    have hhl : L.mulRel h l r.val := hH.mul_spec h' l'
    have hqh : L.mulRel q.val h r.val := by
      have he : q*h' = r := by simp only [q,r,mul_assoc,inv_mul_cancel,_root_.mul_one]
      have hm := hH.mul_spec q h'
      change L.mulRel q.val h (q*h').val at hm
      simpa only [he] using hm
    obtain ⟨x,hsk,hht⟩ := hdom3.triple L (hHA hh) (hBA hb) (hHA hk) hhs hbk
    obtain ⟨y,hry,hhy⟩ := hdom3.triple L (hHA hh) (hHA hl) (hBA hb) hhl hlb
    have hey : y = x := L.unique hhy hht
    obtain ⟨z,hrz,hqsz⟩ := hdom3.triple L (hHA q.property) (hHA hh) (hBA hb) hqh hhs
    have hez : z = x := (L.unique hrz hry).trans hey
    exact ⟨q.val,q.property,x,hsk,hez ▸ hqsz⟩
end LocalGroupAlgebra
end DirectedCycles
