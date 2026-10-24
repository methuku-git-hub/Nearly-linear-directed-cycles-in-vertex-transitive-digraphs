import DirectedCycles.SeparatedExpansion
import DirectedCycles.CayleyWordTails

set_option autoImplicit false
namespace DirectedCycles

/-- Explicit retained data for one cycle. The level determines whether an
edge is fixed or is a connector. The endpoint equations are word equations. -/
structure ExpansionTemplate (G I : Type*) [Group G] (a : G) (l : I → ℕ) (D : ℕ) where
  length : ℕ
  two_le : 2 ≤ length
  vertex : Fin length ↪ G
  position : Fin length → I
  level : Fin length → ℕ
  level_le : ∀ e, level e ≤ l (position e)
  choice : Fin length → Fin (D+1)
  label : Fin length → G
  fixed_end : ∀ e, level e < l (position e) →
    vertex (finRotate length e) = vertex e*a
  connector_end : ∀ e, level e = l (position e) →
    vertex (finRotate length e) =
      vertex e*a^(choice e).val*label e*a^(D-(choice e).val)
  connector_level : ∀ e, level e = l (position e) → level (finRotate length e) = 0

namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

def pointCount (E : ExpansionTemplate G I a l D) (e : Fin E.length) : ℕ :=
  if E.level e < l (E.position e) then 1 else D+1

/-- All points are explicit powers of the start or end of the auxiliary edge. -/
def point (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (k : Fin (E.pointCount e)) : G :=
  if E.level e < l (E.position e) then E.vertex e
  else if k.val ≤ (E.choice e).val then E.vertex e*a^k.val
  else E.vertex (finRotate E.length e)*a^(-((D+1-k.val : ℕ) : ℤ))

/-- Tag the outgoing and incoming pieces by the separated intervals. -/
def tag (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (k : Fin (E.pointCount e)) : ExpansionPosition I l D :=
  if he : E.level e < l (E.position e) then ⟨E.position e,.fixed ⟨E.level e,he⟩⟩
  else if hk : k.val ≤ (E.choice e).val then
    ⟨E.position e,.outgoing ⟨k.val,lt_of_le_of_lt hk (E.choice e).isLt⟩⟩
  else ⟨E.position (finRotate E.length e),.incoming ⟨D-k.val,by
    have hki : k.val < D+1 := by simpa only [pointCount,he,ite_false] using k.isLt
    have hc := (E.choice e).isLt
    omega⟩⟩

theorem tag_fixed (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (k : Fin (E.pointCount e)) (he : E.level e < l (E.position e)) :
    E.tag e k = ⟨E.position e,.fixed ⟨E.level e,he⟩⟩ := by
  unfold tag
  rw [dite_eq_left he]

theorem tag_outgoing (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (k : Fin (E.pointCount e)) (he : ¬ E.level e < l (E.position e))
    (hk : k.val ≤ (E.choice e).val) :
    E.tag e k = ⟨E.position e,.outgoing ⟨k.val,lt_of_le_of_lt hk (E.choice e).isLt⟩⟩ := by
  unfold tag
  rw [dite_eq_right he,dite_eq_left hk]

theorem tag_incoming (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (k : Fin (E.pointCount e)) (he : ¬ E.level e < l (E.position e))
    (hk : ¬ k.val ≤ (E.choice e).val) :
    E.tag e k = ⟨E.position (finRotate E.length e),.incoming ⟨D-k.val,by
      have hki : k.val < D+1 := by simpa only [pointCount,he,ite_false] using k.isLt
      omega⟩⟩ := by
  unfold tag
  rw [dite_eq_right he,dite_eq_right hk]

/-- Recover the local path index from a band; this also handles a one-point
fixed edge. -/
def _root_.DirectedCycles.ExpansionBand.localIndex {l D : ℕ} : ExpansionBand l D → ℕ
  | .fixed _ => 0
  | .outgoing k => k.val
  | .incoming k => D-k.val

theorem tag_index (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (k : Fin (E.pointCount e)) : (E.tag e k).2.localIndex = k.val := by
  by_cases he : E.level e < l (E.position e)
  · rw [E.tag_fixed e k he]
    have hki : k.val < 1 := by simpa only [pointCount,he,ite_true] using k.isLt
    change 0 = k.val
    omega
  · by_cases hk : k.val ≤ (E.choice e).val
    · rw [E.tag_outgoing e k he hk]
      rfl
    · rw [E.tag_incoming e k he hk]
      have hki : k.val < D+1 := by simpa only [pointCount,he,ite_false] using k.isLt
      change D-(D-k.val) = k.val
      omega

theorem tag_injective (E : ExpansionTemplate G I a l D) (e : Fin E.length) :
    Function.Injective (E.tag e) := by
  intro i j he
  apply Fin.ext
  have h := congrArg (fun z : ExpansionPosition I l D => z.2.localIndex) he
  simpa only [E.tag_index] using h

theorem point_anchor (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (k : Fin (E.pointCount e)) :
    E.point e k = E.vertex (expansionAnchorIndex (finRotate E.length) e (E.tag e k).2)*
      a^((E.tag e k).2.anchorOffset) := by
  by_cases he : E.level e < l (E.position e)
  · rw [E.tag_fixed e k he]
    simp only [point,he,ite_true,expansionAnchorIndex,ExpansionBand.anchorOffset,zpow_zero,mul_one]
  · by_cases hk : k.val ≤ (E.choice e).val
    · rw [E.tag_outgoing e k he hk]
      simp only [point,he,hk,ite_false,ite_true,expansionAnchorIndex,ExpansionBand.anchorOffset,zpow_natCast]
    · rw [E.tag_incoming e k he hk]
      have hki : k.val < D+1 := by simpa only [pointCount,he,ite_false] using k.isLt
      simp only [point,he,hk,ite_false,expansionAnchorIndex,ExpansionBand.anchorOffset]
      congr 2
      omega

end ExpansionTemplate
end DirectedCycles
