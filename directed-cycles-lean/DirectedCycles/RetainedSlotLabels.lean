import DirectedCycles.RetainedLayers

set_option autoImplicit false
namespace DirectedCycles

/-- At an interior run position, the actual retained slot is the fixed a-edge. -/
theorem cyclicLiftSlots_get_fixed {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) (k : Fin ((data[i.val]).1+1))
    (hk : k.val < (data[i.val]).1) :
    (cyclicLiftSlots a D data)[(retainedPositionEquiv a D data ⟨i,k⟩).val]'(by
      simpa only [cyclicLiftSlots_length,cyclicBaselineWord_length] using
        (retainedPositionEquiv a D data ⟨i,k⟩).isLt) = runSlot a := by
  have hf := flatBlock_get (fun z : ℕ × G => List.replicate z.1 (runSlot a) ++ [connectorSlot a z.2 D])
    data i k.val (by simp only [List.length_append,List.length_replicate,List.length_singleton]; omega)
  have hoff : flatBlockOffset (fun z : ℕ × G => List.replicate z.1 (runSlot a) ++ [connectorSlot a z.2 D]) data i =
      ((data.take i.val).map (fun z => z.1+1)).sum := cyclicLiftSlots_length a D (data.take i.val)
  simp only [hoff] at hf
  rw [List.getElem_append_left (by simpa only [List.length_replicate] using hk),List.getElem_replicate] at hf
  simpa only [retainedPositionEquiv_val,cyclicLiftSlots] using hf

/-- At the final retained run position, the actual slot has exactly the D+1
connector alternatives. -/
theorem cyclicLiftSlots_get_final {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) (k : Fin ((data[i.val]).1+1))
    (hk : k.val = (data[i.val]).1) :
    (cyclicLiftSlots a D data)[(retainedPositionEquiv a D data ⟨i,k⟩).val]'(by
      simpa only [cyclicLiftSlots_length,cyclicBaselineWord_length] using
        (retainedPositionEquiv a D data ⟨i,k⟩).isLt) = connectorSlot a (data[i.val]).2 D := by
  have h := cyclicLiftSlots_get_connector a D data i
  simpa only [retainedPositionEquiv_val,hk,connectorPosition] using h

/-- The label set at the cyclic layer is the label set of its actual retained
slot, expressed without any assumed positional correspondence. -/
theorem slotLabels_retainedLayer {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (hne : data ≠ [])
    [NeZero (slotBaseline (cyclicLiftSlots a D data)).length]
    (p : RetainedPosition data) :
    slotLabels (cyclicLiftSlots a D data) (retainedLayerEquiv a D data hne p) =
      ((cyclicLiftSlots a D data)[(retainedPositionEquiv a D data p).val]'(by
        simpa only [cyclicLiftSlots_length,cyclicBaselineWord_length] using
          (retainedPositionEquiv a D data p).isLt)).labels := by
  unfold slotLabels
  simp only [retainedLayerEquiv_val]

end DirectedCycles
