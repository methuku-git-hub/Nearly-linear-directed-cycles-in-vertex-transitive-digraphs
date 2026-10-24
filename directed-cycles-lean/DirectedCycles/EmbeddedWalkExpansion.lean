import DirectedCycles.TemplateEdgeCondition

set_option autoImplicit false
namespace DirectedCycles

/-- Walk expansion also applies when the cycle's vertices are embedded
in a larger digraph, as for the root orbit of a semiregular action. -/
theorem embedded_walk_expansion {G V : Type*} [Group G] {R : Digraph G} {D : Digraph V}
    (C : Cycle R) (a : G) (hclosed : C.ClosedUnderGenerator a) (f : G ↪ V)
    (P : ∀ i, SimplePath D (f (C.vertex i)) (f (C.vertex (finRotate C.length i))))
    (hinter : ∀ i j z, z ∈ (P i).vertices.dropLast → z ∈ (P j).vertices.dropLast →
      C.vertex i = C.vertex j ∨
      C.vertex (finRotate C.length i) = C.vertex (finRotate C.length j) ∨
      C.vertex (finRotate C.length j) = C.vertex i*a ∨
      C.vertex (finRotate C.length i) = C.vertex j*a) :
    ∃ L : Cycle D, C.length ≤ L.length := by
  let E : Digraph V := fun x y => ∃ u v, R u v ∧ f u = x ∧ f v = y
  let Q : Cycle E := C.map f (fun u v huv => ⟨u,v,huv,rfl,rfl⟩)
  let τ := fun i : Fin Q.length => f (C.vertex i*a)
  obtain ⟨L,_,hL,_⟩ := walk_expansion Q τ P (by
    intro i j z hi hj
    rcases hinter i j z hi hj with he | he | he | he
    · exact Or.inl (congrArg f he)
    · exact Or.inr (Or.inl (congrArg f he))
    · exact Or.inr (Or.inr (Or.inl (congrArg f he)))
    · exact Or.inr (Or.inr (Or.inr (congrArg f he)))) (by
      intro i j hij
      have he : C.vertex i*a = C.vertex j := f.injective hij
      have hc := hclosed i ⟨j,he.symm⟩
      exact (C.vertex.injective (hc.trans he)).symm)
  exact ⟨L,hL⟩

end DirectedCycles
