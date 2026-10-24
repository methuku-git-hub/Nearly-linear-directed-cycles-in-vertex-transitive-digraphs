import DirectedCycles.LocalEquivalenceWindow

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace EquivalenceWindow
variable {G : Type*} {L : LocalGroupAlgebra G} {S W : Set G}
    (C : L.EquivalenceWindow S) (hWS : W ⊆ S)
    (hW1 : L.one ∈ W) (hdom : L.AllProductsDefined W 3)
    (hW3 : L.wordPower W 3 ⊆ S)

include hW1 hdom hW3 in
/-- The small-window quotient is associative even though representative
changes need not preserve the small multiplication domain. All comparisons
are performed in the larger equivalence window using actual triple products. -/
theorem mul_assoc {a b c ab bc x y : C.Carrier hWS}
    (hab : C.mulRel hWS a b ab) (hbc : C.mulRel hWS b c bc)
    (hx : C.mulRel hWS ab c x) (hy : C.mulRel hWS a bc y) : x = y := by
  obtain ⟨a1,b1,p1,ha1,hb1,hp1,hprod1⟩ := hab
  obtain ⟨b2,c2,p2,hb2,hc2,hp2,hprod2⟩ := hbc
  obtain ⟨p3,c3,zL,hp3,hc3,hzL,hprodL⟩ := hx
  obtain ⟨a4,p4,zR,ha4,hp4,hzR,hprodR⟩ := hy
  obtain ⟨t,ht⟩ := hdom [a1.val,b1.val,c2.val] (by simp) (by aesop)
  obtain ⟨u,hu⟩ := hdom [a1.val,b2.val,c2.val] (by simp) (by aesop)
  have htS : t ∈ S := hW3 ⟨[a1.val,b1.val,c2.val],rfl,by aesop,ht⟩
  have huS : u ∈ S := hW3 ⟨[a1.val,b2.val,c2.val],rfl,by aesop,hu⟩
  obtain ⟨v,w,hv,hw,hm⟩ := ht.split L (a := [a1.val,b1.val]) (b := [c2.val]) rfl (by simp) (by simp)
  have hvp : v = p1.val := L.unique ((Product.pair_iff L _ _ _).1 hv) hprod1
  have hwc : w = c2.val := (Product.singleton_iff L).1 hw
  have hpt : L.mulRel p1.val c2.val t := by simpa only [hvp,hwc] using hm
  obtain ⟨v',w',hv',hw',hm'⟩ := hu.split L (a := [a1.val]) (b := [b2.val,c2.val]) rfl (by simp) (by simp)
  have hva : v' = a1.val := (Product.singleton_iff L).1 hv'
  have hwp : w' = p2.val := L.unique ((Product.pair_iff L _ _ _).1 hw') hprod2
  have hap : L.mulRel a1.val p2.val u := by simpa only [hva,hwp] using hm'
  obtain ⟨a',r,ha',hr,har⟩ := ht.split L (a := [a1.val]) (b := [b1.val,c2.val]) rfl (by simp) (by simp)
  have hea : a' = a1.val := (Product.singleton_iff L).1 ha'
  have hart : L.mulRel a1.val r t := by simpa only [hea] using har
  have hrS : r ∈ S := by
    apply hW3
    apply L.wordPower_subset_wordPower hW1 hdom (by omega : 2 ≤ 3) le_rfl
    exact ⟨[b1.val,c2.val],rfl,by aesop,hr⟩
  have hLt : C.Rel zL.val t :=
    C.mul_rel p3.val (hWS p3.property) c3.val (hWS c3.property) zL.val (hWS zL.property)
      p1.val (hWS p1.property) c2.val (hWS c2.property) t htS hprodL hpt
      (Quotient.exact (hp3.trans hp1.symm)) (Quotient.exact (hc3.trans hc2.symm))
  have hRu : C.Rel zR.val u :=
    C.mul_rel a4.val (hWS a4.property) p4.val (hWS p4.property) zR.val (hWS zR.property)
      a1.val (hWS a1.property) p2.val (hWS p2.property) u huS hprodR hap
      (Quotient.exact (ha4.trans ha1.symm)) (Quotient.exact (hp4.trans hp2.symm))
  have hrp : C.Rel r p2.val :=
    C.mul_rel b1.val (hWS b1.property) c2.val (hWS c2.property) r hrS
      b2.val (hWS b2.property) c2.val (hWS c2.property) p2.val (hWS p2.property)
      ((Product.pair_iff L _ _ _).1 hr) hprod2 (Quotient.exact (hb1.trans hb2.symm))
      (C.refl _ (hWS c2.property))
  have htu : C.Rel t u := C.mul_rel a1.val (hWS a1.property) r hrS t htS
    a1.val (hWS a1.property) p2.val (hWS p2.property) u huS hart hap
    (C.refl _ (hWS a1.property)) hrp
  have hLu : C.Rel zL.val u := C.trans _ (hWS zL.property) _ htS _ huS hLt htu
  have hLR : C.Rel zL.val zR.val := C.trans _ (hWS zL.property) _ huS _ (hWS zR.property)
    hLu (C.symm _ (hWS zR.property) _ huS hRu)
  rw [← hzL,← hzR]
  exact Quotient.sound hLR
end EquivalenceWindow
end LocalGroupAlgebra
end DirectedCycles
