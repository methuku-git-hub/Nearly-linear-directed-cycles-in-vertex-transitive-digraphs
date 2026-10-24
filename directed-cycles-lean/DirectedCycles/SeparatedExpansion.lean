import DirectedCycles.ExpansionBands
import DirectedCycles.PowerCosetCoordinates

set_option autoImplicit false
namespace DirectedCycles

/-- The quotient position together with its local expansion band. -/
abbrev ExpansionPosition (I : Type*) (l : I → ℕ) (D : ℕ) :=
  (i : I) × ExpansionBand (l i) D

/-- Numeric coordinates distinguish every band at every quotient position. -/
theorem expansionPosition_coordinates_injective {I : Type*} (l : I → ℕ) (D h : ℕ)
    (hgap : ∀ i, l i+2*D+2 ≤ h) :
    Function.Injective (fun z : ExpansionPosition I l D =>
      (z.1, (⟨z.2.coordinate h,z.2.coordinate_lt (hgap z.1)⟩ : Fin h))) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have hi : i = j := congrArg Prod.fst he
  subst j
  have hc := congrArg (fun z : I × Fin h => z.2.val) he
  have hxy := ExpansionBand.coordinate_injective (hgap i) hc
  change x = y at hxy
  subst y
  rfl

/-- Incoming points are anchored at the edge end; other points at its start. -/
def expansionAnchorIndex {J : Type*} {l D : ℕ} (next : J → J) (j : J) : ExpansionBand l D → J
  | .fixed _ => j
  | .outgoing _ => j
  | .incoming _ => next j

/-- The signed distance from the appropriate edge anchor. -/
def ExpansionBand.anchorOffset {l D : ℕ} : ExpansionBand l D → ℤ
  | .fixed _ => 0
  | .outgoing k => k.val
  | .incoming k => -((k.val : ℤ)+1)

/-- Separation proof for actual point families once their explicit quotient
coordinates and start/end formulas have been established. No disjointness or
simple-path conclusion is assumed. -/
theorem separated_expansion_points_injective {G Q I J : Type*} [Group G] [Group Q]
    (a : G) (q : G →* Q) (l : I → ℕ) (D h : ℕ)
    (hgap : ∀ i, l i+2*D+2 ≤ h) (r : I → Q)
    (hcoord : Function.Injective (fun z : I × Fin h => r z.1*(q a)^z.2.val))
    (next : J ↪ J) (x : J ↪ G) (m : J → ℕ)
    (point : ∀ j, Fin (m j) → G)
    (tag : ∀ j, Fin (m j) → ExpansionPosition I l D)
    (htag : ∀ j, Function.Injective (tag j))
    (hproj : ∀ j k, q (point j k) = r (tag j k).1*(q a)^((tag j k).2.coordinate h))
    (hanchor : ∀ j k, point j k =
      x (expansionAnchorIndex next j (tag j k).2)*a^((tag j k).2.anchorOffset)) :
    Function.Injective (fun z : (j : J) × Fin (m j) => point z.1 z.2) := by
  rintro ⟨j,k⟩ ⟨j',k'⟩ he
  change point j k = point j' k' at he
  have ht : tag j k = tag j' k' := by
    apply expansionPosition_coordinates_injective l D h hgap
    apply hcoord
    exact (hproj j k).symm.trans ((congrArg q he).trans (hproj j' k'))
  have hj : j = j' := by
    have hv := he
    rw [hanchor j k,hanchor j' k'] at hv
    rw [← ht] at hv
    have ha := x.injective (mul_right_cancel hv)
    cases hb : (tag j k).2 with
    | fixed b => simpa only [hb,expansionAnchorIndex] using ha
    | outgoing b => simpa only [hb,expansionAnchorIndex] using ha
    | incoming b => exact next.injective (by simpa only [hb,expansionAnchorIndex] using ha)
  subst j'
  have hk := htag j ht
  subst k'
  rfl

end DirectedCycles
