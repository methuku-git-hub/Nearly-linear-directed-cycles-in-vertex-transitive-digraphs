module

public import DirectedCycles.SpanningEquivalence
public import DirectedCycles.SpanningLiftInput
public import DirectedCycles.AuxiliaryLayerBound
public import DirectedCycles.AuxiliaryGroupIndex
public import DirectedCycles.ActualFixedFibres

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem AbovePrimeCutoff.of_card_dvd {G H : Type*} {D : ℕ}
    (h : AbovePrimeCutoff G D) (hd : Nat.card H ∣ Nat.card G) : AbovePrimeCutoff H D :=
  fun p hp hd' => h p hp (hd'.trans hd)

/-- A spanning quotient cycle forces the actual auxiliary group to be B.
The strengthened lower-class input therefore gives spanning in the precise
B-coordinates used by the expansion theorem. -/
theorem chosen_auxiliary_spanning_cycle {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (a : G) (S : Set G) (n : ℕ)
    (hn : Group.nilpotencyClass G ≤ n) (input : ChosenLiftInput a S (n+1))
    (hspan : SpansTruncation (n+1) (Set.range (fun i : Fin input.data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes input.data i.castSucc))))
    (b eta : ℝ) (hlayer : LayerSpanningBound (elementCommutators a) (n+1) b eta)
    (hprime : AbovePrimeCutoff (elementCommutators a) (n+1)) :
    ∃ Q : Cycle (cyclicAuxiliaryGraph a (n+1) input.data input.nonempty),
      b*(slotBaseline (cyclicLiftSlots a (n+1) input.data)).length*
        (Nat.card (elementCommutators a) : ℝ)^(1-eta) ≤ Q.length ∧
      ∀ z, SpansTruncation (n+1)
        (auxiliaryLayerCoordinates a (n+1) input.data input.nonempty Q z) := by
  let U := cyclicAuxiliaryGroup a (n+1) input.data input.nonempty
  have he : U = elementCommutators a := auxiliary_group_eq_elementCommutators_of_spanning
    a n hn input.data input.nonempty input.nu input.endpoint input.congruence hspan
  let e : U ≃* elementCommutators a := MulEquiv.subgroupCongr he
  have hbound : LayerSpanningBound U (n+1) b eta :=
    layerSpanningBound_equiv e (n+1) b eta hlayer
  obtain ⟨Q,hQ,hQspan⟩ := hbound _ input.two_le_layers _
    (cyclicAuxiliary_labels_nonempty a (n+1) input.data input.nonempty)
    (cyclicAuxiliaryGraph_stronglyConnected a (n+1) input.data input.nonempty)
  refine ⟨Q,?_,?_⟩
  · rw [Nat.card_congr e.toEquiv] at hQ
    exact hQ
  · intro z
    have hpU : AbovePrimeCutoff U (n+1) := by
      intro p hp hd
      apply hprime p hp
      rwa [← Nat.card_congr e.toEquiv]
    apply ((hQspan hpU z).image e.toMonoidHom e.surjective).mono
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨i,hi⟩ := hy
    exact ⟨i,congrArg Prod.snd hi,congrArg (fun v => v.1.val) hi⟩

end DirectedCycles
