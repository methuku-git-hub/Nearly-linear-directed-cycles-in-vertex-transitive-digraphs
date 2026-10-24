import DirectedCycles.NormalizedLayerLabels
import DirectedCycles.ConnectorAlgebra

set_option autoImplicit false
namespace DirectedCycles

/-- The endpoint prefix is reset to one on the closing edge. -/
def closingPrefix {G : Type*} [Group G] (xs : List G) (j : Fin xs.length) : G :=
  if j.val+1 < xs.length then (xs.take (j.val+1)).prod else 1

/-- The actual coordinate label between baseline prefixes. -/
def coordinateLabel {G : Type*} [Group G] (xs : List G) (j : Fin xs.length) (a : G) : G :=
  (xs.take j.val).prod*a*(closingPrefix xs j)⁻¹

/-- Normalization gives identity baseline labels except at the closing edge,
where the label is precisely the baseline product. -/
theorem coordinateLabel_baseline {G : Type*} [Group G] (xs : List G) (j : Fin xs.length) :
    coordinateLabel xs j xs[j.val] = if j.val+1 < xs.length then 1 else xs.prod := by
  have he : (xs.take (j.val+1)).prod = (xs.take j.val).prod*xs[j.val] := by
    rw [← List.take_concat_get' xs j.val j.isLt,List.prod_append,List.prod_singleton]
  dsimp only [coordinateLabel,closingPrefix]
  split_ifs with h
  · rw [he,mul_inv_cancel]
  · have hj : j.val+1 = xs.length := by omega
    rw [hj,List.take_length] at he
    rw [inv_one,mul_one,he]

/-- Equality of alternative words modulo a normal subgroup puts every
coordinate label in that subgroup, once the baseline closes modulo it. -/
theorem coordinateLabel_mem_normal {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (xs : List G) (hprod : xs.prod ∈ N) (j : Fin xs.length) (a : G)
    (ha : QuotientGroup.mk' N a = QuotientGroup.mk' N xs[j.val]) :
    coordinateLabel xs j a ∈ N := by
  have hb : coordinateLabel xs j xs[j.val] ∈ N := by
    rw [coordinateLabel_baseline]
    split_ifs
    · exact N.one_mem
    · exact hprod
  have he : QuotientGroup.mk' N (coordinateLabel xs j a) =
      QuotientGroup.mk' N (coordinateLabel xs j xs[j.val]) := by
    simp only [coordinateLabel,map_mul,map_inv,ha]
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N (coordinateLabel xs j a) = 1
  rw [he]
  exact (QuotientGroup.eq_one_iff _).mpr hb

/-- Every connector alternative has the same image modulo B=[G,a]. -/
theorem connectorWord_quotient {G : Type*} [Group G] (a s : G) (D j : ℕ) (hj : j ≤ D) :
    QuotientGroup.mk' (elementCommutators a) (connectorWord a s D j) =
      QuotientGroup.mk' (elementCommutators a) (a^D*s) := by
  let q := QuotientGroup.mk' (elementCommutators a)
  have hc : Commute (q a) (q s) := (Subgroup.mem_center_iff.mp
    (element_mod_commutators_central a) (q s)).symm
  change q (a^j*s*a^(D-j)) = q (a^D*s)
  rw [map_mul,map_mul,map_mul,map_pow,map_pow,map_pow,mul_assoc,
    (hc.pow_left (D-j)).eq.symm,← mul_assoc,← pow_add,Nat.add_sub_of_le hj]

end DirectedCycles
