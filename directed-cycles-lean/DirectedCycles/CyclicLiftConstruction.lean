import DirectedCycles.AuxiliaryGroupIndex

set_option autoImplicit false
namespace DirectedCycles

/-- The exact baseline-and-relative-label generating set for the actual
constructed group, with all labels in baseline-prefix coordinates. -/
theorem cyclicAuxiliaryGroup_generators {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ []) :
    cyclicAuxiliaryGroup a D data hne = Subgroup.closure
      (normalizedRelativeLabels (cyclicAuxiliaryLabels a D data hne)
        (normalizedBaseline (slotBaseline (cyclicLiftSlots a D data)))) := by
  let xs := slotBaseline (cyclicLiftSlots a D data)
  let : NeZero xs.length := ⟨Nat.ne_of_gt (cyclicLiftSlots_baseline_length_pos a D data hne)⟩
  apply normalizedLayer_generation (cyclicAuxiliaryLabels a D data hne) (normalizedBaseline xs)
    (normalizedBaseline_length xs)
  · exact normalizedCoordinate_baseline_allowed xs _ (slotBaseline_allowed (cyclicLiftSlots a D data))
  · intro j hj
    exact normalizedBaseline_prefix xs j (by simpa only [normalizedBaseline_length] using hj)

/-- Construction 5.3: the actual cyclic lift, its exact layer count, its
containment in B, strong connectivity, and the claimed generator description.
The integer congruence is the manuscript's baseline closure condition. -/
theorem cyclic_lift_construction {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ []) (nu : ℤ)
    (hnu : QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod =
      (QuotientGroup.mk' (elementCommutators a) a)^nu)
    (hcong : (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) : ℤ) ∣
      ((data.map (fun z => z.1+D)).sum : ℤ)+nu) :
    (slotBaseline (cyclicLiftSlots a D data)).length = (data.map (fun z => z.1+1)).sum ∧
    cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a ∧
    StronglyConnected (cyclicAuxiliaryGraph a D data hne) ∧
    cyclicAuxiliaryGroup a D data hne = Subgroup.closure
      (normalizedRelativeLabels (cyclicAuxiliaryLabels a D data hne)
        (normalizedBaseline (slotBaseline (cyclicLiftSlots a D data)))) := by
  refine ⟨?_,cyclicAuxiliaryGroup_le_of_congruence a D data hne nu hnu hcong,
    cyclicAuxiliaryGraph_stronglyConnected a D data hne,cyclicAuxiliaryGroup_generators a D data hne⟩
  rw [slotBaseline_length,cyclicLiftSlots_length]

end DirectedCycles
