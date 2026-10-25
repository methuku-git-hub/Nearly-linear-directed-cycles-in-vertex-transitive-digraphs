module

public import DirectedCycles.ConnectorEndpointSeparation
public import DirectedCycles.CollisionConstraintDegree

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The forbidden differences selected for right-multiplication
constraints exclude every mixed collision between distinct connectors. -/
theorem connector_mixed_separated {Q H I K : Type*} [Group Q] [Group H]
    (a : Q) [NeZero (orderOf a)] (p : Q →* H) (hpa : p a = 1)
    (start finish : I → Q) (hs : Function.Injective (fun i => p (start i)))
    (hf : Function.Injective (fun i => p (finish i))) (t : K → Q)
    (e : RightCollision ⟨fun i => p (start i),hs⟩ ⟨fun i => p (finish i),hf⟩
      (fun k => p (t k)) → ZMod (orderOf a))
    (hoffset : ∀ c, start c.val.2.1*t c.val.1*(finish c.val.2.2)⁻¹ = residuePower a (e c))
    (D : ℕ) (v : I → ZMod (orderOf a))
    (havoid : ∀ c, v c.val.2.2-v c.val.2.1 ∉ collisionForbiddenResidues (orderOf a) D (e c))
    (i j : I) (hij : i ≠ j) (k : K) (u u' : ℕ) (hu : u ≤ D) (hu' : u' ≤ D) :
    residuePower a (v j+u')*finish j ≠ (residuePower a (v i+u)*start i)*t k := by
  intro he
  have hp := congrArg p he
  simp only [map_mul,map_residuePower_eq_one a p hpa,one_mul] at hp
  let c : RightCollision ⟨fun i => p (start i),hs⟩ ⟨fun i => p (finish i),hf⟩
      (fun k => p (t k)) := ⟨(k,i,j),hp.symm,hij⟩
  exact no_mixed_residue_collision a (start i) (finish j) (t k) (e c) (v i) (v j)
    D u u' hu hu' (hoffset c) (havoid c) he

end DirectedCycles
