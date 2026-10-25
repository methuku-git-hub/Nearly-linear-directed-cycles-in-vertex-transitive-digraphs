module

public import DirectedCycles.CyclicLayerWords

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A group isomorphism gives the exact cyclic-layer graph isomorphism when
available labels are transported with it. -/
theorem cyclicLayer_equiv_arc {G H : Type*} [Group G] [Group H] {T : ℕ}
    (e : G ≃* H) (S : ZMod T → Set G) (x y : G × ZMod T) :
    CyclicLayerDigraph (fun i => e.symm ⁻¹' S i) (e x.1,x.2) (e y.1,y.2) ↔
      CyclicLayerDigraph S x y := by
  constructor
  · rintro ⟨hz,a,ha,hy⟩
    refine ⟨hz,e.symm a,ha,?_⟩
    have h := congrArg e.symm hy
    simpa only [map_mul,MulEquiv.symm_apply_apply] using h
  · rintro ⟨hz,a,ha,hy⟩
    refine ⟨hz,e a,?_,?_⟩
    · simpa only [Set.mem_preimage,MulEquiv.symm_apply_apply] using ha
    · rw [hy,map_mul]

/-- The layer estimate is only requested for at least two layers in the
lifting theorem. The one-vertex one-layer loop convention is therefore absent
from this hypothesis rather than being accidentally asserted for `Cycle`. -/
def LayerCycleLowerBound (G : Type*) [Group G] (b eta : ℝ) : Prop :=
  ∀ T : ℕ, 2 ≤ T → ∀ S : ZMod T → Set G, (∀ i, (S i).Nonempty) →
    StronglyConnected (CyclicLayerDigraph S) →
    ∃ C : Cycle (CyclicLayerDigraph S), b*T*(Nat.card G : ℝ)^(1-eta) ≤ C.length

/-- The layer lower bound is invariant under an actual group isomorphism. -/
theorem layerCycleLowerBound_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (b eta : ℝ) (hH : LayerCycleLowerBound H b eta) :
    LayerCycleLowerBound G b eta := by
  intro T hT S hne hsc
  let f : G × ZMod T ≃ H × ZMod T := e.toEquiv.prodCongr (Equiv.refl _)
  have hne' : ∀ i, (e.symm ⁻¹' S i).Nonempty := by
    intro i
    obtain ⟨a,ha⟩ := hne i
    exact ⟨e a,by simpa only [Set.mem_preimage,MulEquiv.symm_apply_apply] using ha⟩
  have hsc' : StronglyConnected (CyclicLayerDigraph (fun i => e.symm ⁻¹' S i)) :=
    stronglyConnected_image f f.surjective
      (fun x y h => (cyclicLayer_equiv_arc e S x y).mpr h) hsc
  obtain ⟨C,hC⟩ := hH T hT (fun i => e.symm ⁻¹' S i) hne' hsc'
  have hback : ∀ x y, CyclicLayerDigraph (fun i => e.symm ⁻¹' S i) x y →
      CyclicLayerDigraph S (f.symm x) (f.symm y) := by
    intro x y h
    apply (cyclicLayer_equiv_arc e S (f.symm x) (f.symm y)).mp
    change CyclicLayerDigraph (fun i => e.symm ⁻¹' S i)
      (e (e.symm x.1),x.2) (e (e.symm y.1),y.2)
    simpa only [MulEquiv.apply_symm_apply] using h
  refine ⟨C.map f.symm.toEmbedding hback,?_⟩
  change b*T*(Nat.card G : ℝ)^(1-eta) ≤ C.length
  rw [Nat.card_congr e.toEquiv]
  exact hC

end DirectedCycles
