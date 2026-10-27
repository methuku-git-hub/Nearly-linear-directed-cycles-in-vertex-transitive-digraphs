module

public import DirectedCycles.NormalizedCoordinateSystem
public import DirectedCycles.RestrictedLayerGroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Realization of a retained coordinate vertex by its actual baseline prefix. -/
def normalizedRealization {G : Type*} [Group G] (xs : List G) (v : G × ZMod xs.length) : G :=
  v.1*(xs.take v.2.val).prod

/-- The cyclic successor uses exactly the reset prefix on the closing edge. -/
theorem closingPrefix_eq_next {G : Type*} [Group G] (xs : List G) [NeZero xs.length]
    (z : ZMod xs.length) :
    closingPrefix xs (coordinateIndex xs z) = (xs.take (z+1).val).prod := by
  have hz : (z+1).val = (z.val+1)%xs.length := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [← Nat.cast_one,← Nat.cast_add,ZMod.val_natCast]
  change (if z.val+1 < xs.length then (xs.take (z.val+1)).prod else 1) = _
  rw [hz]
  have hlt := ZMod.val_lt z
  split_ifs with hh
  · rw [Nat.mod_eq_of_lt hh]
  · have he : z.val+1 = xs.length := by omega
    rw [he,Nat.mod_self,List.take_zero,List.prod_nil]

/-- Each normalized auxiliary edge realizes its defining group word exactly. -/
theorem normalizedRealization_edge {G : Type*} [Group G] (xs : List G) [NeZero xs.length]
    (S : ZMod xs.length → Set G) (C : Subgroup G)
    (x y : C × ZMod xs.length)
    (hxy : CyclicLayerDigraph (restrictedLayerLabels (normalizedLabelSet xs S) C) x y) :
    ∃ w ∈ S x.2,
      normalizedRealization xs (y.1.val,y.2) = normalizedRealization xs (x.1.val,x.2)*w := by
  obtain ⟨hz,mu,hmu,hy⟩ := hxy
  obtain ⟨w,hw,he⟩ := hmu
  refine ⟨w,hw,?_⟩
  have hy' : y.1.val = x.1.val*mu.val := congrArg Subtype.val hy
  change y.1.val*(xs.take y.2.val).prod = (x.1.val*(xs.take x.2.val).prod)*w
  rw [hy',hz,← he]
  change (x.1.val*((xs.take x.2.val).prod*w*(closingPrefix xs (coordinateIndex xs x.2))⁻¹))*
    (xs.take (x.2+1).val).prod = _
  rw [closingPrefix_eq_next]
  group

/-- Distinct quotient baseline prefixes make the retained realization injective
for every subgroup in the normal fibre. -/
theorem normalizedRealization_injective {G Q : Type*} [Group G] [Group Q]
    (xs : List G) (q : G →* Q) (C : Subgroup G) (hC : C ≤ q.ker)
    (hp : Function.Injective (fun z : ZMod xs.length => q (xs.take z.val).prod)) :
    Function.Injective (fun v : C × ZMod xs.length => normalizedRealization xs (v.1.val,v.2)) := by
  rintro ⟨x,i⟩ ⟨y,j⟩ he
  change x.val*(xs.take i.val).prod = y.val*(xs.take j.val).prod at he
  have hi : i = j := by
    apply hp
    have hx : q x.val = 1 := hC x.property
    have hy : q y.val = 1 := hC y.property
    simpa only [map_mul,hx,hy,one_mul] using congrArg q he
  subst j
  have hxy : x = y := Subtype.ext (mul_right_cancel he)
  subst y
  rfl

end DirectedCycles
