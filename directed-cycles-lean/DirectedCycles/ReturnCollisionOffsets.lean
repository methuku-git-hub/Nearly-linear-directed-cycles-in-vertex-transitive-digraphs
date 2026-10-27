module

public import DirectedCycles.CyclicResiduePowers
public import DirectedCycles.CollisionConstraintDegree

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Every actual collision constraint has a cyclic offset modulo B.
Its existence is derived from equality of the K-cosets. -/
theorem element_collision_offset {G : Type*} [Group G] [Finite G]
    (a g g' t : G)
    (he : QuotientGroup.mk' (elementClosure a) g * QuotientGroup.mk' (elementClosure a) t =
      QuotientGroup.mk' (elementClosure a) g') :
    ∃ e : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a)),
      QuotientGroup.mk' (elementCommutators a) g * QuotientGroup.mk' (elementCommutators a) t *
        (QuotientGroup.mk' (elementCommutators a) g')⁻¹ =
        residuePower (QuotientGroup.mk' (elementCommutators a) a) e := by
  let b := QuotientGroup.mk' (elementCommutators a) a
  let : NeZero (orderOf b) := ⟨(orderOf_pos b).ne'⟩
  have hmem : g*t*g'⁻¹ ∈ elementClosure a := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (elementClosure a) (g*t*g'⁻¹) = 1
    rw [map_mul,map_mul,map_inv,he,mul_inv_cancel]
  obtain ⟨n,hn⟩ := elementClosure_quotient_power a (g*t*g'⁻¹) hmem
  refine ⟨(n : ZMod (orderOf b)),?_⟩
  rw [residuePower_intCast,← map_inv,← map_mul,← map_mul]
  exact hn

end DirectedCycles
