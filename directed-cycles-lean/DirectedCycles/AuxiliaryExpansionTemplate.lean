module

public import DirectedCycles.RetainedSlotLabels
public import DirectedCycles.RetainedSeparation
public import DirectedCycles.ExpansionTemplate

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Every actual auxiliary edge has exactly a fixed word or one of the
constructed connector words, according to its retained position. -/
theorem cyclicAuxiliary_edge_words {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (x y : cyclicAuxiliaryGroup a D data hne × ZMod (slotBaseline (cyclicLiftSlots a D data)).length)
    (hxy : cyclicAuxiliaryGraph a D data hne x y) :
    let p := (retainedLayerEquiv a D data hne).symm x.2
    let rx := normalizedRealization (slotBaseline (cyclicLiftSlots a D data)) (x.1.val,x.2)
    let ry := normalizedRealization (slotBaseline (cyclicLiftSlots a D data)) (y.1.val,y.2)
    ∃ j : Fin (D+1),
      (p.2.val < (data[p.1.val]).1 → ry = rx*a) ∧
      (p.2.val = (data[p.1.val]).1 → ry = rx*a^j.val*(data[p.1.val]).2*a^(D-j.val)) := by
  let : NeZero (slotBaseline (cyclicLiftSlots a D data)).length :=
    ⟨Nat.ne_of_gt (cyclicLiftSlots_baseline_length_pos a D data hne)⟩
  let p := (retainedLayerEquiv a D data hne).symm x.2
  obtain ⟨w,hw,hend⟩ := normalizedRealization_edge (slotBaseline (cyclicLiftSlots a D data))
    (slotLabels (cyclicLiftSlots a D data)) (cyclicAuxiliaryGroup a D data hne) x y hxy
  have hz : x.2 = retainedLayerEquiv a D data hne p :=
    ((retainedLayerEquiv a D data hne).apply_symm_apply x.2).symm
  rw [hz,slotLabels_retainedLayer] at hw
  by_cases hp : p.2.val < (data[p.1.val]).1
  · rw [cyclicLiftSlots_get_fixed a D data p.1 p.2 hp] at hw
    have hw' : w = a := hw
    subst w
    refine ⟨⟨0,Nat.zero_lt_succ D⟩,fun _ => hend,?_⟩
    intro h
    have h' : p.2.val = (data[p.1.val]).1 := h
    exact (Nat.ne_of_lt hp h').elim
  · have hp' : p.2.val = (data[p.1.val]).1 := by have := p.2.isLt; omega
    rw [cyclicLiftSlots_get_final a D data p.1 p.2 hp'] at hw
    obtain ⟨j,hj⟩ := hw
    refine ⟨j,fun h => (hp h).elim,fun _ => ?_⟩
    rw [← hj] at hend
    simpa only [connectorWord,mul_assoc] using hend

/-- The template used in the separation proof is extracted from the actual
auxiliary cycle; its vertices, levels, labels and word endpoints are proved. -/
noncomputable def cyclicAuxiliary_expansionTemplate {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hC : cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a)
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hl : ∀ i : Fin data.length, (data[i.val]).1 < orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (Q : Cycle (cyclicAuxiliaryGraph a D data hne)) :
    ExpansionTemplate G (Fin data.length) a (fun i => (data[i.val]).1) D := by
  classical
  let pos : Fin Q.length → RetainedPosition data := fun e => (retainedLayerEquiv a D data hne).symm (Q.vertex e).2
  let x : Fin Q.length ↪ G := Q.vertex.trans ⟨fun v => normalizedRealization
    (slotBaseline (cyclicLiftSlots a D data)) (v.1.val,v.2),
      cyclicAuxiliary_realization_injective a D data hne hC hr hl⟩
  have hw := fun e => cyclicAuxiliary_edge_words a D data hne (Q.vertex e)
    (Q.vertex (finRotate Q.length e)) (Q.arc e)
  refine {
    length := Q.length
    two_le := Q.two_le
    vertex := x
    position := fun e => (pos e).1
    level := fun e => (pos e).2.val
    level_le := fun e => Nat.le_of_lt_succ (pos e).2.isLt
    choice := fun e => Classical.choose (hw e)
    label := fun e => (data[(pos e).1.val]).2
    fixed_end := ?_
    connector_end := ?_
    connector_level := ?_
  }
  · intro e he
    exact (Classical.choose_spec (hw e)).1 he
  · intro e he
    exact (Classical.choose_spec (hw e)).2 he
  · intro e he
    have hz : (Q.vertex (finRotate Q.length e)).2 = (Q.vertex e).2+1 := (Q.arc e).1
    change ((retainedLayerEquiv a D data hne).symm (Q.vertex (finRotate Q.length e)).2).2.val = 0
    rw [hz,retainedLayerEquiv_symm_next]
    exact retainedNext_connector_level data (pos e) he

end DirectedCycles
