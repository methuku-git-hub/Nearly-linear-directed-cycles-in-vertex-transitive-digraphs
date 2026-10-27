module

public import DirectedCycles.ExpansionTemplate

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Backwards powers occupy the upper end of one finite cyclic interval. -/
theorem negative_power_wrapped {Q : Type*} [Group Q] (a : Q) (h k : ℕ)
    (hh : a^h = 1) (hk : k ≤ h) : a^(-((k : ℕ) : ℤ)) = a^(h-k) := by
  have he : ((h-k : ℕ) : ℤ) = (h : ℤ)+ -(k : ℤ) := by omega
  rw [← zpow_natCast a (h-k),he,zpow_add,zpow_natCast,hh,one_mul]

namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- The formulas for every interior point have exactly the interval
coordinates used in the separation argument. -/
theorem point_projection {Q : Type*} [Group Q] (E : ExpansionTemplate G I a l D)
    (q : G →* Q) (h : ℕ) (hgap : ∀ i, l i+2*D+2 ≤ h)
    (hpow : (q a)^h = 1) (r : I → Q)
    (hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e))
    (e : Fin E.length) (k : Fin (E.pointCount e)) :
    q (E.point e k) = r (E.tag e k).1*(q a)^((E.tag e k).2.coordinate h) := by
  by_cases he : E.level e < l (E.position e)
  · rw [E.tag_fixed e k he]
    simpa only [point,he,ite_true,ExpansionBand.coordinate] using hx e
  · by_cases hk : k.val ≤ (E.choice e).val
    · have hlevel : E.level e = l (E.position e) := le_antisymm (E.level_le e) (by omega)
      rw [E.tag_outgoing e k he hk]
      simp only [point,he,hk,ite_false,ite_true]
      simp only [map_mul,map_pow,hx e,hlevel,ExpansionBand.coordinate,pow_add,mul_assoc]
    · have hlevel : E.level e = l (E.position e) := le_antisymm (E.level_le e) (by omega)
      have hz := E.connector_level e hlevel
      have hki : k.val < D+1 := by simpa only [pointCount,he,ite_false] using k.isLt
      have hkh : D+1-k.val ≤ h := by have := hgap (E.position e); omega
      rw [E.tag_incoming e k he hk]
      simp only [point,he,hk,ite_false,map_mul,map_zpow,
        hx (finRotate E.length e),hz,pow_zero,mul_one,
        negative_power_wrapped (q a) h _ hpow hkh,ExpansionBand.coordinate]
      congr 2
      omega

/-- Actual start and end formulas, distinct retained vertices, and the
quotient interval bounds force global injectivity of all expanded points. -/
theorem points_injective {Q : Type*} [Group Q] (E : ExpansionTemplate G I a l D)
    (q : G →* Q) (h : ℕ) (hgap : ∀ i, l i+2*D+2 ≤ h)
    (hpow : (q a)^h = 1) (r : I → Q)
    (hcoord : Function.Injective (fun z : I × Fin h => r z.1*(q a)^z.2.val))
    (hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e)) :
    Function.Injective (fun z : (e : Fin E.length) × Fin (E.pointCount e) => E.point z.1 z.2) := by
  apply separated_expansion_points_injective a q l D h hgap r hcoord
    (finRotate E.length).toEmbedding E.vertex E.pointCount E.point E.tag E.tag_injective
  · exact E.point_projection q h hgap hpow r hx
  · exact E.point_anchor

end ExpansionTemplate
end DirectedCycles
