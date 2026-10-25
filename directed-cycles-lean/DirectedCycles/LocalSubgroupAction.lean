module

public import DirectedCycles.LocalGlobalSubgroup
public import DirectedCycles.LocalWordPowers
public import DirectedCycles.LocalTwoProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} {L : LocalGroupAlgebra G} {H A B : Set G}

/-- A genuine subgroup acts totally on its one-sided thickening of B. All
needed products are justified by the three-letter ambient domain. -/
theorem IsGlobalSubgroup.mul_thickening (hH : L.IsGlobalSubgroup H)
    (hHA : H ⊆ A) (hBA : B ⊆ A) (hdom : L.AllProductsDefined A 3)
    {h : G} (hh : h ∈ H) {s : G} (hs : s ∈ L.setMul H B) :
    ∃ z ∈ L.setMul H B, L.mulRel h s z := by
  obtain ⟨k,hk,b,hb,hks⟩ := hs
  have hhA := hHA hh
  have hkA := hHA hk
  have hbA := hBA hb
  obtain ⟨z,hz⟩ := hdom [h,k,b] (by simp) (by aesop)
  obtain ⟨a,t,ha,ht,hat⟩ := hz.split L (a := [h]) (b := [k,b]) rfl (by simp) (by simp)
  have he : a = h := (Product.singleton_iff L).1 ha
  have hts : t = s := L.unique ((Product.pair_iff L k b t).1 ht) hks
  have hhz : L.mulRel h s z := by simpa only [he,hts] using hat
  obtain ⟨c,d,hc,hd,hcd⟩ := hz.split L (a := [h,k]) (b := [b]) rfl (by simp) (by simp)
  have hed : d = b := (Product.singleton_iff L).1 hd
  obtain ⟨w,hw,hm⟩ := hH.mul_total h hh k hk
  have hec : c = w := L.unique ((Product.pair_iff L h k c).1 hc) hm
  exact ⟨z,⟨w,hw,b,hb,by simpa only [hec,hed] using hcd⟩,hhz⟩

/-- The total action on the thickening is an actual Lean group action, with
its action law proved from defined local associativity. -/
@[instance_reducible] noncomputable def IsGlobalSubgroup.thickeningMulAction (hH : L.IsGlobalSubgroup H)
    (hHA : H ⊆ A) (hBA : B ⊆ A) (hdom : L.AllProductsDefined A 3) :
    letI := hH.toGroup
    MulAction H (L.setMul H B) := by
  let := hH.toGroup
  let S := L.setMul H B
  let act : H → S → S := fun h s =>
    ⟨Classical.choose (hH.mul_thickening hHA hBA hdom h.property s.property),
      (Classical.choose_spec (hH.mul_thickening hHA hBA hdom h.property s.property)).1⟩
  have hspec : ∀ h : H, ∀ s : S, L.mulRel h.val s.val (act h s).val :=
    fun h s => (Classical.choose_spec (hH.mul_thickening hHA hBA hdom h.property s.property)).2
  exact { smul := act
          one_smul := by
            intro s
            exact Subtype.ext (L.unique (hspec 1 s) (L.one_mul s.val))
          mul_smul := by
            intro h k s
            exact Subtype.ext (L.assoc (hH.mul_spec h k) (hspec k s)
              (hspec (h*k) s) (hspec h (act k s))) }
end LocalGroupAlgebra
end DirectedCycles
