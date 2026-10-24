import DirectedCycles.LayerSlots
import DirectedCycles.CyclicBaselineWords

set_option autoImplicit false
namespace DirectedCycles

/-- A fixed edge in a distinguished-generator run. -/
def runSlot {G : Type*} [Group G] (a : G) : LayerSlot G := ⟨a,{a},rfl⟩

/-- All D+1 alternatives of a compressed connector, with j=D as baseline. -/
def connectorSlot {G : Type*} [Group G] (a s : G) (D : ℕ) : LayerSlot G where
  baseline := a^D*s
  labels := Set.range (fun j : Fin (D+1) => connectorWord a s D j.val)
  baseline_mem := ⟨⟨D,by omega⟩,by simp [connectorWord]⟩

/-- The actual retained positions: each run contributes l fixed slots and one
connector slot. -/
def cyclicLiftSlots {G : Type*} [Group G] (a : G) (D : ℕ) (data : List (ℕ × G)) :
    List (LayerSlot G) := data.flatMap (fun z => List.replicate z.1 (runSlot a) ++ [connectorSlot a z.2 D])

/-- The retained-position count is exactly the manuscript's sum (l_i+1). -/
theorem cyclicLiftSlots_length {G : Type*} [Group G] (a : G) (D : ℕ) (data : List (ℕ × G)) :
    (cyclicLiftSlots a D data).length = (data.map (fun z => z.1+1)).sum := by
  induction data with
  | nil => rfl
  | cons z data ih =>
    change (List.replicate z.1 (runSlot a) ++ [connectorSlot a z.2 D] ++ cyclicLiftSlots a D data).length = _
    simp only [List.length_append,List.length_replicate,List.length_singleton,ih,List.map_cons,List.sum_cons]

/-- The baseline recorded in the slots is exactly the constructed baseline word. -/
theorem cyclicLiftSlots_baseline {G : Type*} [Group G] (a : G) (D : ℕ) (data : List (ℕ × G)) :
    slotBaseline (cyclicLiftSlots a D data) = cyclicBaselineWord a D data := by
  induction data with
  | nil => rfl
  | cons z data ih =>
    change ((List.replicate z.1 (runSlot a) ++ [connectorSlot a z.2 D] ++ cyclicLiftSlots a D data).map LayerSlot.baseline) = _
    simp only [List.map_append,List.map_replicate,List.map_singleton]
    rw [show (cyclicLiftSlots a D data).map LayerSlot.baseline = cyclicBaselineWord a D data from ih]
    rfl

/-- Every slot alternative agrees with its baseline modulo B. -/
theorem cyclicLiftSlots_quotient {G : Type*} [Group G] (a : G) (D : ℕ) (data : List (ℕ × G)) :
    ∀ z ∈ cyclicLiftSlots a D data, ∀ w ∈ z.labels,
      QuotientGroup.mk' (elementCommutators a) w = QuotientGroup.mk' (elementCommutators a) z.baseline := by
  intro z hz
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hz
  rcases List.mem_append.mp hp with hr | hc
  · have he : z = runSlot a := (List.mem_replicate.mp hr).2
    subst z
    intro w hw
    have he : w = a := hw
    rw [he]
    rfl
  · have he : z = connectorSlot a p.2 D := List.mem_singleton.mp hc
    subst z
    rintro w ⟨j,rfl⟩
    exact connectorWord_quotient a p.2 D j.val (by omega)

end DirectedCycles
