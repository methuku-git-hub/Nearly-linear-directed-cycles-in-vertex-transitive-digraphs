import DirectedCycles.CyclicAuxiliaryGraph

set_option autoImplicit false
namespace DirectedCycles

@[simp] theorem slotLabels_natCast {G : Type*} [Group G] (slots : List (LayerSlot G))
    [NeZero (slotBaseline slots).length] (j : Fin slots.length) :
    slotLabels slots (j.val : ZMod (slotBaseline slots).length) = (slots[j.val]).labels := by
  have hval : (j.val : ZMod (slotBaseline slots).length).val = j.val :=
    ZMod.val_natCast_of_lt (by simpa only [slotBaseline_length] using j.isLt)
  have hi : (j.val : ZMod (slotBaseline slots).length).val < slots.length := by
    simpa only [slotBaseline_length] using ZMod.val_lt (j.val : ZMod (slotBaseline slots).length)
  exact congrArg LayerSlot.labels (congrArg (fun k : Fin slots.length => slots[k.val])
    (show (⟨(j.val : ZMod (slotBaseline slots).length).val,hi⟩ : Fin slots.length) = j from Fin.ext hval))

/-- Every displayed coordinate label belongs to the actual round subgroup. -/
theorem slotCoordinate_label_mem {G : Type*} [Group G]
    (slots : List (LayerSlot G)) [NeZero (slotBaseline slots).length]
    (j : Fin slots.length) (w : G) (hw : w ∈ (slots[j.val]).labels) :
    coordinateLabel (slotBaseline slots) ⟨j.val,by simpa only [slotBaseline_length] using j.isLt⟩ w ∈
      Subgroup.closure (layerRoundProducts (normalizedLabelSet (slotBaseline slots) (slotLabels slots))) := by
  let xs := slotBaseline slots
  let k : Fin xs.length := ⟨j.val,by simpa only [xs,slotBaseline_length] using j.isLt⟩
  have hmem : coordinateLabel xs k w ∈ normalizedLabelSet xs (slotLabels slots) (k.val : ZMod xs.length) := by
    change coordinateLabel xs k w ∈ coordinateLabel xs (coordinateIndex xs (k.val : ZMod xs.length)) '' _
    rw [coordinateIndex_natCast]
    apply Set.mem_image_of_mem
    change w ∈ slotLabels slots (j.val : ZMod (slotBaseline slots).length)
    rw [slotLabels_natCast slots j]
    exact hw
  exact normalizedLayer_labels_mem (normalizedLabelSet xs (slotLabels slots)) (normalizedBaseline xs)
    (normalizedBaseline_length xs) (normalizedCoordinate_baseline_allowed xs _ (slotBaseline_allowed slots))
    (fun t ht => normalizedBaseline_prefix xs t (by simpa only [normalizedBaseline_length] using ht))
    _ _ hmem

end DirectedCycles
