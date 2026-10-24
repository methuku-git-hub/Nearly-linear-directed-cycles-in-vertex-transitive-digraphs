import DirectedCycles.NilpotentCycleBounds

set_option autoImplicit false
namespace DirectedCycles

theorem one_layer_rounds {G : Type*} [Group G] (S : ZMod 1 → Set G) :
    layerRoundProducts S = S 0 := by
  ext x
  constructor
  · rintro ⟨xs,hlen,hxs,hprod⟩
    obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hlen
    have ha : a = x := by simpa only [List.prod_cons,List.prod_nil,mul_one] using hprod
    exact ha ▸ hxs.1
  · intro hx
    exact ⟨[x],rfl,⟨hx,trivial⟩,by simp⟩

/-- A single cyclic layer on a nontrivial group is precisely its Cayley
digraph; the correspondence preserves both simplicity and spanning. -/
theorem one_layer_cycle_from_cayley {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (D : ℕ) (b eps : ℝ) (hbound : CayleySpanningBound G D b eps)
    (S : ZMod 1 → Set G) (hsc : StronglyConnected (CyclicLayerDigraph S)) :
    ∃ C : Cycle (CyclicLayerDigraph S), b*(Nat.card G : ℝ)^(1-eps) ≤ C.length ∧
      (AbovePrimeCutoff G D → ∀ z, SpansTruncation D (C.layerCoordinates z)) := by
  have hgen : Subgroup.closure (S 0) = ⊤ := by
    rw [← one_layer_rounds S]
    exact cyclicLayer_rounds_generate S hsc
  obtain ⟨C,hC,hspan⟩ := hbound inferInstance (S 0) hgen
  let e : G × ZMod 1 ≃ G := Equiv.prodUnique _ _
  have hmap : ∀ x y, CayleyDigraph (S 0) x y → CyclicLayerDigraph S (e.symm x) (e.symm y) := by
    rintro x y ⟨a,ha,hy⟩
    refine ⟨Subsingleton.elim _ _,a,?_,hy⟩
    rwa [show (e.symm x).2 = 0 from Subsingleton.elim _ _]
  let L := C.map e.symm.toEmbedding hmap
  refine ⟨L,hC,?_⟩
  intro hp z
  have hcoords : L.layerCoordinates z = Set.range C.vertex := by
    ext x
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i,congrArg Prod.fst hi⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,Prod.ext rfl (Subsingleton.elim _ _)⟩
  rw [hcoords]
  exact hspan hp

end DirectedCycles
