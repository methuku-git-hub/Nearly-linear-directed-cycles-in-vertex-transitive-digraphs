module

public import DirectedCycles.ConnectorPositions
public import DirectedCycles.SlotCoordinateMembership
public import DirectedCycles.CyclicAuxiliaryGraph

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The constructed cyclic lift supplies every input of the algebraic connector
index theorem. Prefixes and labels are extracted from their actual retained positions. -/
theorem cyclicAuxiliary_connector_data {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hclose : (QuotientGroup.mk' (elementCommutators a) a)^((data.map (fun z => z.1+D)).sum) *
        QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod = 1) :
    ∃ p t : Fin data.length → G, ∃ mu : Fin data.length → Fin (D+1) → elementCommutators a,
      (∀ i, ∃ k ∈ elementClosure a, p i = k*cycleLabelPrefixes data i.castSucc) ∧
      (∀ i j, (mu i j).val = p i*connectorWord a (data[i.val]).2 D j.val*(t i)⁻¹) ∧
      (∀ i j, mu i j ∈ (cyclicAuxiliaryGroup a D data hne).subgroupOf (elementCommutators a)) := by
  let slots := cyclicLiftSlots a D data
  let xs := slotBaseline slots
  let : NeZero xs.length := ⟨Nat.ne_of_gt (cyclicLiftSlots_baseline_length_pos a D data hne)⟩
  let pos : Fin data.length → Fin slots.length := fun i => ⟨connectorPosition data i,connectorPosition_lt a D data i⟩
  let idx : Fin data.length → Fin xs.length := fun i => ⟨(pos i).val,by
    simpa only [xs,slotBaseline_length] using (pos i).isLt⟩
  let p : Fin data.length → G := fun i => (xs.take (idx i).val).prod
  let t : Fin data.length → G := fun i => closingPrefix xs (idx i)
  let label : Fin data.length → Fin (D+1) → G := fun i j =>
    coordinateLabel xs (idx i) (connectorWord a (data[i.val]).2 D j.val)
  have hlabel : ∀ i j, label i j ∈ cyclicAuxiliaryGroup a D data hne := by
    intro i j
    apply slotCoordinate_label_mem slots (pos i)
    change connectorWord a (data[i.val]).2 D j.val ∈ (slots[(pos i).val]).labels
    change connectorWord a (data[i.val]).2 D j.val ∈
      ((cyclicLiftSlots a D data)[connectorPosition data i]'(connectorPosition_lt a D data i)).labels
    rw [cyclicLiftSlots_get_connector]
    exact ⟨j,rfl⟩
  have hCB := cyclicAuxiliaryGroup_le a D data hne hclose
  let mu : Fin data.length → Fin (D+1) → elementCommutators a :=
    fun i j => ⟨label i j,hCB (hlabel i j)⟩
  refine ⟨p,t,mu,?_,?_,?_⟩
  · intro i
    change ∃ k ∈ elementClosure a,
      ((slotBaseline (cyclicLiftSlots a D data)).take (connectorPosition data i)).prod =
        k*cycleLabelPrefixes data i.castSucc
    rw [cyclicLiftSlots_baseline]
    exact connectorPosition_prefix_coset a D data i
  · intro i j
    rfl
  · intro i j
    exact hlabel i j

end DirectedCycles
