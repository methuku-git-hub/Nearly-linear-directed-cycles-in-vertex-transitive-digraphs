import DirectedCycles.LocalProductCompression
import DirectedCycles.LocalTwoProducts

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Removing an adjacent inverse pair preserves the value whenever the
original and shortened all-bracketings products are defined. -/
theorem Product.cancel_pair_value {a b : List G} {g x y : G}
    (hlong : L.Product (a ++ [g,L.inv g] ++ b) x) (hshort : L.Product (a++b) y) : x = y := by
  obtain ⟨u,v,hu,hv,hm⟩ := hshort.split_allow_empty L rfl
  have hblocks : List.Forall₂ L.Product [a,[g,L.inv g],b] [u,L.one,v] :=
    List.Forall₂.cons hu (List.Forall₂.cons ((Product.pair_iff L _ _ _).2 (L.mul_inv g))
      (List.Forall₂.cons hv List.Forall₂.nil))
  have hflat : L.Product [a,[g,L.inv g],b].flatten x := by
    simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using hlong
  have hthree := hflat.compress L hblocks
  obtain ⟨s,t,hs,ht,hst⟩ := hthree.split L (a := [u]) (b := [L.one,v]) rfl (by simp) (by simp)
  have hsu : s = u := (Product.singleton_iff L).1 hs
  have htv : t = v := L.unique ((Product.pair_iff L _ _ _).1 ht) (L.one_mul v)
  have huvx : L.mulRel u v x := by simpa only [hsu,htv] using hst
  exact L.unique huvx hm

/-- Cancellation supplies the actual shortened product once its existence
has been established from the ambient domain. -/
theorem Product.cancel_pair {a b : List G} {g x : G}
    (hlong : L.Product (a ++ [g,L.inv g] ++ b) x)
    (hshort : ∃ y, L.Product (a++b) y) : L.Product (a++b) x := by
  obtain ⟨y,hy⟩ := hshort
  exact (hlong.cancel_pair_value L hy).symm ▸ hy

theorem Product.cancel_inv_pair {a b : List G} {g x : G}
    (hlong : L.Product (a ++ [L.inv g,g] ++ b) x)
    (hshort : ∃ y, L.Product (a++b) y) : L.Product (a++b) x := by
  have hh : L.Product (a ++ [L.inv g,L.inv (L.inv g)] ++ b) x := by
    simpa only [L.inv_inv] using hlong
  exact hh.cancel_pair L hshort
end LocalGroupAlgebra
end DirectedCycles
