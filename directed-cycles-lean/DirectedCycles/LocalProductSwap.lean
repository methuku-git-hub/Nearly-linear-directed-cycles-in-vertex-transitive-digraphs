module

public import DirectedCycles.LocalProductCancellation
public import DirectedCycles.LocalMinimalEscape

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Swapping adjacent commuting factors preserves an all-bracketings
product when both word domains are established. -/
theorem Product.swap_pair_value {a b : List G} {g h x y : G}
    (hgh : L.Commute g h)
    (hleft : L.Product (a ++ [g,h] ++ b) x)
    (hright : L.Product (a ++ [h,g] ++ b) y) : x = y := by
  obtain ⟨u,r,hu,hr,_⟩ := hleft.split_allow_empty L (a := a) (b := [g,h]++b) (by simp only [List.append_assoc])
  obtain ⟨v,w,hv,hw,_⟩ := hr.split_allow_empty L rfl
  obtain ⟨z,hgz,hzg⟩ := hgh
  have hb : List.Forall₂ L.Product [a,[g,h],b] [u,z,w] :=
    List.Forall₂.cons hu (List.Forall₂.cons ((Product.pair_iff L _ _ _).2 hgz)
      (List.Forall₂.cons hw List.Forall₂.nil))
  have hb' : List.Forall₂ L.Product [a,[h,g],b] [u,z,w] :=
    List.Forall₂.cons hu (List.Forall₂.cons ((Product.pair_iff L _ _ _).2 hzg)
      (List.Forall₂.cons hw List.Forall₂.nil))
  have hx : L.Product [a,[g,h],b].flatten x := by
    simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using hleft
  have hy : L.Product [a,[h,g],b].flatten y := by
    simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using hright
  exact (hx.compress L hb).unique L (hy.compress L hb')
end LocalGroupAlgebra
end DirectedCycles
