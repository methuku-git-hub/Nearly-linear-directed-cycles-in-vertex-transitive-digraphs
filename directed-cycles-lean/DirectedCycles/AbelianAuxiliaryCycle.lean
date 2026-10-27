module

public import DirectedCycles.AbelianNormalClosure
public import DirectedCycles.SubsingletonLayers
public import DirectedCycles.AuxiliaryLayerBound
public import DirectedCycles.ActualFixedFibres

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The actual abelian auxiliary group is trivial; its Hamiltonian layer
cycle supplies all B-coordinates, without assuming the layer bound. -/
theorem abelian_auxiliary_cycle {G : Type*} [CommGroup G] [Finite G]
    (a : G) (S : Set G) (D : ℕ) (input : ChosenLiftInput a S D) :
    ∃ Q : Cycle (cyclicAuxiliaryGraph a D input.data input.nonempty),
      (slotBaseline (cyclicLiftSlots a D input.data)).length ≤ Q.length ∧
      ∀ z, auxiliaryLayerCoordinates a D input.data input.nonempty Q z = Set.univ := by
  let U := cyclicAuxiliaryGroup a D input.data input.nonempty
  have hU : U ≤ elementCommutators a := cyclicAuxiliaryGroup_le_of_congruence a D input.data
    input.nonempty input.nu input.endpoint input.congruence
  have hbot : U = ⊥ := by rw [abelian_elementCommutators] at hU; exact le_bot_iff.mp hU
  let : Subsingleton U := by rw [hbot]; infer_instance
  obtain ⟨Q,hQ,hs⟩ := subsingleton_layer_hamiltonian input.two_le_layers
    (restrictedLayerLabels (cyclicAuxiliaryLabels a D input.data input.nonempty) U)
    (cyclicAuxiliaryGraph_stronglyConnected a D input.data input.nonempty)
  refine ⟨Q,hQ,?_⟩
  intro z
  apply Set.eq_univ_of_forall
  intro b
  obtain ⟨e,he⟩ := hs (1,z)
  refine ⟨e,congrArg Prod.snd he,?_⟩
  have hb : b.val = 1 := by have := b.property; simpa only [abelian_elementCommutators,Subgroup.mem_bot] using this
  rw [he,hb]
  rfl

end DirectedCycles
