module

public import DirectedCycles.CyclicLiftSlots
public import DirectedCycles.FlatMapPositions
public import DirectedCycles.BaselineQuotientPrefixes

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The number of retained positions before the i-th connector. -/
def connectorPosition {G : Type*} (data : List (ℕ × G)) (i : Fin data.length) : ℕ :=
  ((data.take i.val).map (fun z => z.1+1)).sum + (data[i.val]).1

theorem connectorPosition_lt {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) :
    connectorPosition data i < (cyclicLiftSlots a D data).length := by
  have h := flatBlock_position_lt (fun z : ℕ × G =>
    List.replicate z.1 (runSlot a) ++ [connectorSlot a z.2 D]) data i (data[i.val]).1 (by simp)
  change (cyclicLiftSlots a D (data.take i.val)).length + (data[i.val]).1 < _ at h
  rw [cyclicLiftSlots_length] at h
  exact h

/-- The indexed retained slot is exactly the corresponding connector slot. -/
theorem cyclicLiftSlots_get_connector {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) :
    (cyclicLiftSlots a D data)[connectorPosition data i]'(connectorPosition_lt a D data i) =
      connectorSlot a (data[i.val]).2 D := by
  have h := flatBlock_get (fun z : ℕ × G =>
    List.replicate z.1 (runSlot a) ++ [connectorSlot a z.2 D]) data i (data[i.val]).1 (by simp)
  have hoff : flatBlockOffset (fun z : ℕ × G =>
      List.replicate z.1 (runSlot a) ++ [connectorSlot a z.2 D]) data i =
      ((data.take i.val).map (fun z => z.1+1)).sum := cyclicLiftSlots_length a D (data.take i.val)
  simp only [hoff] at h
  rw [List.getElem_append_right (show (List.replicate (data[i.val]).1 (runSlot a)).length ≤
    (data[i.val]).1 by simp)] at h
  simp only [List.length_replicate,Nat.sub_self,List.getElem_cons_zero] at h
  exact h

/-- The baseline prefix before the connector is exactly the earlier blocks
followed by its fixed run. -/
theorem cyclicBaseline_take_connector {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) :
    (cyclicBaselineWord a D data).take (connectorPosition data i) =
      cyclicBaselineWord a D (data.take i.val) ++ List.replicate (data[i.val]).1 a := by
  have h := flatBlock_take (fun z : ℕ × G => runConnectorBlock a D z.1 z.2)
    data i (data[i.val]).1 (by simp)
  have hoff : flatBlockOffset (fun z : ℕ × G => runConnectorBlock a D z.1 z.2) data i =
      ((data.take i.val).map (fun z => z.1+1)).sum := cyclicBaselineWord_length a D (data.take i.val)
  simp only [hoff] at h
  have ht : (runConnectorBlock a D (data[i.val]).1 (data[i.val]).2).take (data[i.val]).1 =
      List.replicate (data[i.val]).1 a := by simp [runConnectorBlock]
  rw [ht] at h
  exact h

/-- Prefix products of the original quotient-cycle labels. -/
def cycleLabelPrefixes {G : Type*} [Group G] (data : List (ℕ × G)) : Fin (data.length+1) → G :=
  fun i => ((data.map Prod.snd).take i.val).prod

@[simp] theorem cycleLabelPrefixes_zero {G : Type*} [Group G] (data : List (ℕ × G)) :
    cycleLabelPrefixes data 0 = 1 := rfl

theorem cycleLabelPrefixes_step {G : Type*} [Group G] (data : List (ℕ × G)) (i : Fin data.length) :
    cycleLabelPrefixes data i.succ = cycleLabelPrefixes data i.castSucc * (data[i.val]).2 := by
  have he := congrArg List.prod (List.take_concat_get' (data.map Prod.snd) i.val (by simpa only [List.length_map] using i.isLt))
  change ((data.map Prod.snd).take (i.val+1)).prod = ((data.map Prod.snd).take i.val).prod * (data[i.val]).2
  simpa only [List.prod_append,List.prod_singleton,List.getElem_map] using he.symm

/-- The actual coordinate prefix has the required K g_i form. -/
theorem connectorPosition_prefix_coset {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) :
    ∃ k ∈ elementClosure a,
      ((cyclicBaselineWord a D data).take (connectorPosition data i)).prod =
        k*cycleLabelPrefixes data i.castSucc := by
  rw [cyclicBaseline_take_connector,List.prod_append,List.prod_replicate]
  have h := cyclicBaseline_connector_prefix a D (data[i.val]).1 (data.take i.val)
  simpa only [List.map_take,cycleLabelPrefixes,Fin.val_castSucc] using h

end DirectedCycles
