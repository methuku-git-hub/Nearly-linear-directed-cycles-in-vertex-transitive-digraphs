module

public import DirectedCycles.DirectedBranchingExtension

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace SimplePath
variable {V : Type*} {D : Digraph V} {root target : V}

def consecutiveArc (P : SimplePath D root target) : Digraph V :=
  fun x y => ∃ i j : Fin P.vertices.length,
    j.val=i.val+1 ∧ P.vertices.get i=x ∧ P.vertices.get j=y

theorem consecutiveArc_chain (P : SimplePath D root target) : P.vertices.IsChain P.consecutiveArc := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  exact ⟨⟨i,by omega⟩,⟨i+1,hi⟩,rfl,rfl,rfl⟩

/-- A specified simple directed path is already a partial outward branching. -/
def toPartialOutBranching [DecidableEq V] (P : SimplePath D root target) :
    PartialOutBranching D root P.vertices.toFinset where
  arc := P.consecutiveArc
  subgraph := by
    rintro x y ⟨i,j,hij,rfl,rfl⟩
    have h := P.chain.getElem i.val (by omega : i.val+1 < P.vertices.length)
    simpa only [List.get_eq_getElem,hij] using h
  support := by
    rintro x y ⟨i,j,_,rfl,rfl⟩
    exact ⟨List.mem_toFinset.mpr (List.get_mem _ _),List.mem_toFinset.mpr (List.get_mem _ _)⟩
  root_mem := List.mem_toFinset.mpr (List.mem_of_head? (P.head ▸ rfl))
  root_no_in := by
    rintro x ⟨i,j,hij,_,hj⟩
    have hpos : 0 < P.vertices.length := List.length_pos_iff.mpr P.nonempty
    have hroot : P.vertices.get ⟨0,hpos⟩ = root := by
      have hh := P.head
      simpa only [List.head?_eq_getElem?,List.getElem?_eq_getElem hpos,Option.some.injEq,
        List.get_eq_getElem] using hh
    have he := List.nodup_iff_injective_get.mp P.nodup (hj.trans hroot.symm)
    have hv := congrArg Fin.val he
    change j.val = 0 at hv
    omega
  unique_in := by
    rintro v x y ⟨i,j,hij,hix,hjv⟩ ⟨k,l,hkl,hky,hlv⟩
    have hjl := List.nodup_iff_injective_get.mp P.nodup (hjv.trans hlv.symm)
    have hv := congrArg Fin.val hjl
    have hik : i = k := Fin.ext (by omega)
    exact hix.symm.trans (hik ▸ hky)
  reachable := by
    intro v hv
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hv)
    have hreach : ∀ k : ℕ, ∀ hk : k < P.vertices.length,
        Reachable P.consecutiveArc root (P.vertices.get ⟨k,hk⟩) := by
      intro k
      induction k with
      | zero =>
        intro hk
        have hh : P.vertices.get ⟨0,hk⟩ = root := by
          have hh := P.head
          simpa only [List.head?_eq_getElem?,List.getElem?_eq_getElem hk,Option.some.injEq,
            List.get_eq_getElem] using hh
        rw [hh]
        exact Relation.ReflTransGen.refl
      | succ k ih =>
        intro hk
        exact (ih (by omega)).tail ⟨⟨k,by omega⟩,⟨k+1,hk⟩,rfl,rfl,rfl⟩
    rw [← hi]
    exact hreach i.val i.isLt

end SimplePath

/-- A prescribed simple root path extends to a spanning out-branching.
The proof adds outward arcs until all vertices are reached. -/
theorem out_branching_containing_path {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} {root target : V} (P : SimplePath D root target)
    (hsc : StronglyConnected D) :
    ∃ B : PartialOutBranching D root Finset.univ, P.vertices.IsChain B.arc := by
  obtain ⟨B,hB⟩ := P.toPartialOutBranching.extends_to_spanning hsc
  refine ⟨B,?_⟩
  exact P.consecutiveArc_chain.imp (fun _ _ h => hB _ _ h)

end DirectedCycles
