import DirectedCycles.LocalGroupProducts
import DirectedCycles.LocalQuotientCancellation
import DirectedCycles.LocalGroupUltraproduct

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Reversal includes existence of the inverse product, not only an equality
conditional on that product being defined. -/
def Reversible : Prop := ∀ {a b c}, L.mulRel a b c → L.mulRel (L.inv b) (L.inv a) (L.inv c)

theorem ofGroup_reversible (G : Type*) [Group G] : (ofGroup G).Reversible := by
  intro a b c h
  change b⁻¹*a⁻¹ = c⁻¹
  change a*b = c at h
  simpa only [mul_inv_rev] using congrArg Inv.inv h

theorem Reversible.restrict (hL : L.Reversible) (S : Set G) (h1 : L.one ∈ S)
    (hi : ∀ x ∈ S, L.inv x ∈ S) : (L.restrict S h1 hi).Reversible :=
  fun h => hL h

/-- Opposite local multiplication has exactly the reversed original domain. -/
def opposite : LocalGroupAlgebra G where
  one := L.one
  inv := L.inv
  mulRel a b c := L.mulRel b a c
  unique := L.unique
  one_mul := L.mul_one
  mul_one := L.one_mul
  inv_mul := L.mul_inv
  mul_inv := L.inv_mul
  assoc := by
    intro a b c ab bc x y hab hbc hx hy
    exact (L.assoc hbc hab hy hx).symm

theorem Product.reverse {l : List G} {x : G} (h : L.Product l x) : L.opposite.Product l.reverse x := by
  induction h with
  | nil => exact Product.nil
  | singleton a => exact Product.singleton a
  | @splits l x hlen u v left right multiply ihl ihr =>
    refine Product.splits (by simpa using hlen)
      (fun a b => v b.reverse a.reverse) (fun a b => u b.reverse a.reverse) ?_ ?_ ?_
    · intro a b hab ha hb
      have he : l = b.reverse++a.reverse := by
        have hh := congrArg List.reverse hab
        simpa only [List.reverse_reverse,List.reverse_append] using hh
      have ha' : a.reverse ≠ [] := by simpa using ha
      have hb' : b.reverse ≠ [] := by simpa using hb
      simpa only [List.reverse_reverse] using ihr b.reverse a.reverse he hb' ha'
    · intro a b hab ha hb
      have he : l = b.reverse++a.reverse := by
        have hh := congrArg List.reverse hab
        simpa only [List.reverse_reverse,List.reverse_append] using hh
      have ha' : a.reverse ≠ [] := by simpa using ha
      have hb' : b.reverse ≠ [] := by simpa using hb
      simpa only [List.reverse_reverse] using ihl b.reverse a.reverse he hb' ha'
    · intro a b hab ha hb
      have he : l = b.reverse++a.reverse := by
        have hh := congrArg List.reverse hab
        simpa only [List.reverse_reverse,List.reverse_append] using hh
      have ha' : a.reverse ≠ [] := by simpa using ha
      have hb' : b.reverse ≠ [] := by simpa using hb
      exact multiply b.reverse a.reverse he hb' ha'
end LocalGroupAlgebra

open scoped Pointwise
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

theorem quotientAlgebra_reversible : (hP.quotientAlgebra hW1 hWi hW6).Reversible :=
  hP.quotient_inverse_product hW1 hWi hW6
end LocalNormalSet

variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

theorem localUltraAlgebra_reversible (hL : ∀ i, (L i).Reversible) :
    (localUltraAlgebra F G L).Reversible := by
  intro a b c
  refine Quotient.inductionOn₃ a b c ?_
  intro a b c h
  apply (localUltraMulRel_mk_iff F G L _ _ _).2
  have hh := (localUltraMulRel_mk_iff F G L a b c).1 h
  exact hh.mono fun i hi => hL i hi
end DirectedCycles
