import DirectedCycles.ChosenLiftInput
import DirectedCycles.LayerEquivalence
import DirectedCycles.SlotCoordinateMembership

set_option autoImplicit false
namespace DirectedCycles

/-- Every actual auxiliary layer has an available label, witnessed by its
constructed baseline and proved containment in the round subgroup. -/
theorem cyclicAuxiliary_labels_nonempty {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ []) :
    ∀ z, (restrictedLayerLabels (cyclicAuxiliaryLabels a D data hne)
      (cyclicAuxiliaryGroup a D data hne) z).Nonempty := by
  let : NeZero (slotBaseline (cyclicLiftSlots a D data)).length :=
    ⟨Nat.ne_of_gt (cyclicLiftSlots_baseline_length_pos a D data hne)⟩
  let xs := slotBaseline (cyclicLiftSlots a D data)
  let S := normalizedLabelSet xs (slotLabels (cyclicLiftSlots a D data))
  have hb := normalizedCoordinate_baseline_allowed xs (slotLabels (cyclicLiftSlots a D data))
    (slotBaseline_allowed (cyclicLiftSlots a D data))
  have hp : ∀ j < (normalizedBaseline xs).length, ((normalizedBaseline xs).take j).prod = 1 :=
    fun j hj => normalizedBaseline_prefix xs j (by simpa only [normalizedBaseline_length] using hj)
  intro z
  obtain ⟨w,hw⟩ := normalizedLayer_nonempty S (normalizedBaseline xs) (normalizedBaseline_length xs) hb z
  have hmem := normalizedLayer_labels_mem S (normalizedBaseline xs) (normalizedBaseline_length xs) hb hp z w hw
  exact ⟨⟨w,hmem⟩,hw⟩

theorem ChosenLiftInput.two_le_layers {G : Type*} [Group G] [Finite G]
    {a : G} {S : Set G} {D : ℕ} (input : ChosenLiftInput a S D) :
    2 ≤ (slotBaseline (cyclicLiftSlots a D input.data)).length := by
  have hsum : ∀ data : List (ℕ × G), data.length ≤ (data.map (fun z => z.1+1)).sum := by
    intro data
    induction data with
    | nil => simp
    | cons z data ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega
  rw [slotBaseline_length,cyclicLiftSlots_length]
  exact input.two_le_length.trans (hsum input.data)

/-- The source subgroup-layer hypothesis applies to the actual auxiliary
group through the proved subgroup-of-B isomorphism. -/
theorem chosen_auxiliary_long_cycle {G : Type*} [Group G] [Finite G]
    (a : G) (S : Set G) (D : ℕ) (input : ChosenLiftInput a S D) (b eta : ℝ)
    (hlayer : ∀ U : Subgroup (elementCommutators a), LayerCycleLowerBound U b eta) :
    ∃ Q : Cycle (cyclicAuxiliaryGraph a D input.data input.nonempty),
      b*(slotBaseline (cyclicLiftSlots a D input.data)).length*
        (Nat.card (cyclicAuxiliaryGroup a D input.data input.nonempty) : ℝ)^(1-eta) ≤ Q.length := by
  let C := cyclicAuxiliaryGroup a D input.data input.nonempty
  have hC : C ≤ elementCommutators a := cyclicAuxiliaryGroup_le_of_congruence a D input.data
    input.nonempty input.nu input.endpoint input.congruence
  let e := Subgroup.subgroupOfEquivOfLe hC
  have hbound : LayerCycleLowerBound C b eta :=
    layerCycleLowerBound_equiv e.symm b eta (hlayer (C.subgroupOf (elementCommutators a)))
  exact hbound _ input.two_le_layers _ (cyclicAuxiliary_labels_nonempty a D input.data input.nonempty)
    (cyclicAuxiliaryGraph_stronglyConnected a D input.data input.nonempty)

end DirectedCycles
