import DirectedCycles.NilpotentCycleBounds
import DirectedCycles.TruncatedFunctor

set_option autoImplicit false
namespace DirectedCycles

/-- Surjective group maps preserve integral additive generation. -/
theorem SpansTruncation.image {G H : Type*} [Group G] [Group H]
    {D : ℕ} {E : Set G} (hE : SpansTruncation D E)
    (f : G →* H) (hf : Function.Surjective f) : SpansTruncation D (f '' E) := by
  let W := AddSubgroup.closure (truncatedElement H D '' (f '' E))
  have hmap : ∀ x ∈ E, truncatedMap f D (truncatedElement G D x) ∈ W := by
    intro x hx
    rw [truncatedMap_element]
    exact AddSubgroup.subset_closure ⟨f x,⟨x,hx,rfl⟩,rfl⟩
  apply top_le_iff.mp
  intro y _
  obtain ⟨x,rfl⟩ := truncatedMap_surjective f hf D y
  exact spansTruncation_map_mem D E hE (truncatedMap f D).toAddMonoidHom W hmap x

/-- The strengthened layer estimate, including its spanning invariant, is
invariant under a group isomorphism. -/
theorem layerSpanningBound_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (D : ℕ) (b eta : ℝ) (hH : LayerSpanningBound H D b eta) :
    LayerSpanningBound G D b eta := by
  intro T hT S hne hsc
  let f : G × ZMod T ≃ H × ZMod T := e.toEquiv.prodCongr (Equiv.refl _)
  have hne' : ∀ i, (e.symm ⁻¹' S i).Nonempty := by
    intro i
    obtain ⟨a,ha⟩ := hne i
    exact ⟨e a,by simpa only [Set.mem_preimage,MulEquiv.symm_apply_apply] using ha⟩
  have hsc' : StronglyConnected (CyclicLayerDigraph (fun i => e.symm ⁻¹' S i)) :=
    stronglyConnected_image f f.surjective
      (fun x y h => (cyclicLayer_equiv_arc e S x y).mpr h) hsc
  obtain ⟨C,hC,hspan⟩ := hH T hT (fun i => e.symm ⁻¹' S i) hne' hsc'
  have hback : ∀ x y, CyclicLayerDigraph (fun i => e.symm ⁻¹' S i) x y →
      CyclicLayerDigraph S (f.symm x) (f.symm y) := by
    intro x y h
    apply (cyclicLayer_equiv_arc e S (f.symm x) (f.symm y)).mp
    change CyclicLayerDigraph (fun i => e.symm ⁻¹' S i)
      (e (e.symm x.1),x.2) (e (e.symm y.1),y.2)
    simpa only [MulEquiv.apply_symm_apply] using h
  let L := C.map f.symm.toEmbedding hback
  refine ⟨L,?_,?_⟩
  · change b*T*(Nat.card G : ℝ)^(1-eta) ≤ C.length
    rw [Nat.card_congr e.toEquiv]
    exact hC
  · intro hp z
    have hp' : AbovePrimeCutoff H D := by
      intro p hpr hd
      apply hp p hpr
      rwa [Nat.card_congr e.toEquiv]
    apply ((hspan hp' z).image e.symm.toMonoidHom e.symm.surjective).mono
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨i,hi⟩ := hy
    exact ⟨i,congrArg f.symm hi⟩

end DirectedCycles
