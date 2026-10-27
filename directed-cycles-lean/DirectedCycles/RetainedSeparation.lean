module

public import DirectedCycles.RetainedPositions
public import DirectedCycles.PowerCosetCoordinates
public import DirectedCycles.NormalizedRealization

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- All actual retained baseline prefixes are different modulo B. This uses
only distinct quotient-cycle positions and retained levels strictly below h. -/
theorem retained_prefixes_injective {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G))
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hl : ∀ i : Fin data.length, (data[i.val]).1 < orderOf (QuotientGroup.mk' (elementCommutators a) a)) :
    Function.Injective (fun j : Fin (cyclicBaselineWord a D data).length =>
      QuotientGroup.mk' (elementCommutators a) ((cyclicBaselineWord a D data).take j.val).prod) := by
  have href : Function.Injective (fun i => QuotientGroup.mk' (elementClosure a) (runReference a D data i)) := by
    intro i j he
    apply hr
    simpa only [runReference_quotient] using he
  have hcoord := element_power_coordinates_injective a (runReference a D data) href
  intro j k he
  obtain ⟨⟨i,u⟩,rfl⟩ := (retainedPositionEquiv a D data).surjective j
  obtain ⟨⟨i',u'⟩,rfl⟩ := (retainedPositionEquiv a D data).surjective k
  simp only [cyclicBaseline_prefix_retained,map_mul,map_pow] at he
  have hu : u.val < orderOf (QuotientGroup.mk' (elementCommutators a) a) := by
    have := u.isLt; have := hl i; omega
  have hu' : u'.val < orderOf (QuotientGroup.mk' (elementCommutators a) a) := by
    have := u'.isLt; have := hl i'; omega
  have hp : (i,(⟨u.val,hu⟩ : Fin (orderOf (QuotientGroup.mk' (elementCommutators a) a)))) =
      (i',⟨u'.val,hu'⟩) := hcoord he
  have hi : i = i' := congrArg Prod.fst hp
  subst i'
  have huu : u = u' := Fin.ext (congrArg (fun z : Fin data.length × Fin
    (orderOf (QuotientGroup.mk' (elementCommutators a) a)) => z.2.val) hp)
  subst u'
  rfl

/-- The actual cyclic layer indices also have distinct baseline images. -/
theorem retained_layer_prefixes_injective {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hl : ∀ i : Fin data.length, (data[i.val]).1 < orderOf (QuotientGroup.mk' (elementCommutators a) a)) :
    Function.Injective (fun z : ZMod (slotBaseline (cyclicLiftSlots a D data)).length =>
      QuotientGroup.mk' (elementCommutators a) ((slotBaseline (cyclicLiftSlots a D data)).take z.val).prod) := by
  let : NeZero (slotBaseline (cyclicLiftSlots a D data)).length :=
    ⟨Nat.ne_of_gt (cyclicLiftSlots_baseline_length_pos a D data hne)⟩
  intro i j he
  have hi : i.val < (cyclicBaselineWord a D data).length := by
    rw [← cyclicLiftSlots_baseline]
    exact ZMod.val_lt i
  have hj : j.val < (cyclicBaselineWord a D data).length := by
    rw [← cyclicLiftSlots_baseline]
    exact ZMod.val_lt j
  have he' : (⟨i.val,hi⟩ : Fin (cyclicBaselineWord a D data).length) = ⟨j.val,hj⟩ :=
    retained_prefixes_injective a D data hr hl (by simpa only [cyclicLiftSlots_baseline] using he)
  exact ZMod.val_injective _ (congrArg Fin.val he')

/-- Actual auxiliary vertices identify injectively with group elements under
the construction's proved subgroup containment and numerical separation. -/
theorem cyclicAuxiliary_realization_injective {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hC : cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a)
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hl : ∀ i : Fin data.length, (data[i.val]).1 < orderOf (QuotientGroup.mk' (elementCommutators a) a)) :
    Function.Injective (fun v : cyclicAuxiliaryGroup a D data hne ×
      ZMod (slotBaseline (cyclicLiftSlots a D data)).length =>
      normalizedRealization (slotBaseline (cyclicLiftSlots a D data)) (v.1.val,v.2)) := by
  apply normalizedRealization_injective _ (QuotientGroup.mk' (elementCommutators a)) _
  · simpa only [QuotientGroup.ker_mk'] using hC
  · exact retained_layer_prefixes_injective a D data hne hr hl

end DirectedCycles
