module

public import DirectedCycles.FunctionalCycles
public import DirectedCycles.LayerWordReplacement
public import DirectedCycles.RoundCycleExpansion

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Repeating a generating baseline round is Hamiltonian. This formulation
proves the full vertex coverage using functional strong connectivity. -/
theorem generating_baseline_hamiltonian {G : Type*} [Group G] [Finite G]
    {T : ℕ} [NeZero T] [Nontrivial (G × ZMod T)]
    (S : ZMod T → Set G) (xs : List G) (hlen : xs.length = T)
    (hxs : LayerWord S 0 xs) (hgen : Subgroup.zpowers xs.prod = ⊤) :
    ∃ C : Cycle (CyclicLayerDigraph S), C.length = T*Nat.card G ∧
      ∀ z : ZMod T, C.layerCoordinates z = Set.univ := by
  classical
  let beta : ZMod T → G := fun z => xs[z.val]'(by rw [hlen]; exact ZMod.val_lt z)
  let B : ZMod T → Set G := fun z => {beta z}
  have hb : ∀ z, beta z ∈ S z := by
    intro z
    simpa only [zero_add,ZMod.natCast_zmod_val] using
      (layerWord_iff_get S 0 xs).mp hxs ⟨z.val,by rw [hlen]; exact ZMod.val_lt z⟩
  have hB : LayerWord B 0 xs := by
    apply (layerWord_iff_get B 0 xs).mpr
    intro j
    have hj : j.val < T := by rw [← hlen]; exact j.isLt
    simp only [B,Set.mem_singleton_iff,zero_add,beta,ZMod.val_natCast_of_lt hj]
  have hround : Subgroup.closure (layerRoundProducts B) = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen]
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨xs,hlen,hB,rfl⟩)
  have hsc := cyclicLayer_stronglyConnected B (fun z => ⟨beta z,rfl⟩) hround
  have hf : ∀ x y z, CyclicLayerDigraph B x y → CyclicLayerDigraph B x z → y = z := by
    rintro x y z ⟨hy,a,ha,hya⟩ ⟨hz,b,hb,hzb⟩
    have ha' : a = beta x.2 := ha
    have hb' : b = beta x.2 := hb
    apply Prod.ext
    · rw [hya,hzb,ha',hb']
    · exact hy.trans hz.symm
  obtain ⟨C,hC,hs⟩ := functional_strong_cycle hf hsc
  have harc : ∀ x y, CyclicLayerDigraph B x y → CyclicLayerDigraph S x y := by
    rintro x y ⟨hz,a,ha,he⟩
    have ha' : a = beta x.2 := ha
    exact ⟨hz,a,ha' ▸ hb x.2,he⟩
  let L := C.map (Function.Embedding.refl _) harc
  refine ⟨L,?_,?_⟩
  · change C.length = T*Nat.card G
    rw [hC,Nat.card_prod,Nat.card_eq_fintype_card (α := ZMod T),ZMod.card,Nat.mul_comm]
  · intro z
    apply Set.eq_univ_of_forall
    intro x
    exact hs (x,z)

end DirectedCycles
