import DirectedCycles.ElementNormalClosure

set_option autoImplicit false
namespace DirectedCycles

/-- In a finite nilpotent group, quotient-generating labels together
with a generate the group. The commutator part of its normal closure
is removed using the proved Frattini generation criterion. -/
theorem nilpotent_generation_from_element_quotient {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (a : G) (S : Set G)
    (hS : Subgroup.closure ((QuotientGroup.mk' (elementClosure a)) '' S) = ⊤) :
    Subgroup.closure (insert a S) = ⊤ := by
  let U := Subgroup.closure (insert a S)
  have ha : a ∈ U := Subgroup.subset_closure (Set.mem_insert a S)
  have hquot : U.map (QuotientGroup.mk' (elementClosure a)) = ⊤ := by
    apply top_unique
    rw [← hS]
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono (Set.image_mono (Set.subset_insert a S))
  have hfull : U ⊔ elementClosure a = ⊤ := by
    apply top_unique
    intro g _
    have hg : QuotientGroup.mk' (elementClosure a) g ∈ U.map (QuotientGroup.mk' (elementClosure a)) := by
      rw [hquot]
      trivial
    obtain ⟨u,hu,he⟩ := hg
    have hk : u⁻¹*g ∈ elementClosure a := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (elementClosure a) (u⁻¹*g) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hm := (U ⊔ elementClosure a).mul_mem ((show U ≤ U ⊔ elementClosure a from le_sup_left) hu)
      ((show elementClosure a ≤ U ⊔ elementClosure a from le_sup_right) hk)
    simpa only [mul_inv_cancel_left] using hm
  apply nilpotent_commutator_nongenerating U
  apply top_unique
  rw [← hfull]
  apply sup_le le_sup_left
  change Subgroup.zpowers a ⊔ elementCommutators a ≤ U ⊔ commutator G
  exact sup_le ((Subgroup.zpowers_le.mpr ha).trans le_sup_left)
    ((elementCommutators_le_derived a).trans le_sup_right)

end DirectedCycles
