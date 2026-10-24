import DirectedCycles.ReturnWalks

set_option autoImplicit false
namespace DirectedCycles

/-- Both tree paths and all their voltage equations can be constructed
from strong connectivity. The returned change of representatives fixes
the chosen root representative. -/
theorem exists_return_spine {G I : Type*} [Group G] [Fintype I] [DecidableEq I]
    (S : I → I → Set G) (root : I) (hsc : StronglyConnected (VoltageDigraph S)) :
    ∃ p : I → G, p root = 1 ∧ Nonempty (ReturnSpine (gaugeLabels S p) root) ∧
      StronglyConnected (VoltageDigraph (gaugeLabels S p)) := by
  classical
  let D : Digraph I := fun i j => (S i j).Nonempty
  have hD : StronglyConnected D := by
    intro i j
    exact reachable_map Prod.snd (fun _ _ h => by obtain ⟨s,hs,_⟩ := h; exact ⟨s,hs⟩)
      (hsc (1,i) (1,j))
  let P : SimplePath D root root := ⟨[root],by simp,rfl,rfl,.singleton root⟩
  obtain ⟨B,A,_,_⟩ := branchings_containing_paths P P hD
  let label : I → I → G := fun i j => if h : B.arc i j then (B.subgraph i j h).choose else 1
  have hlabel : ∀ i j, B.arc i j → label i j ∈ S i j := by
    intro i j h
    simp only [label,dite_eq_left h]
    exact (B.subgraph i j h).choose_spec
  let p := fun i => B.potential label i (Finset.mem_univ i)
  have hp := gauge_outward_tree B S label hlabel
  change p root = 1 ∧ ∀ x y, B.arc x y → 1 ∈ gaugeLabels S p x y at hp
  let S' := gaugeLabels S p
  have hne : ∀ i j, D i j → (S' i j).Nonempty := by
    intro i j hij
    obtain ⟨s,hs⟩ := hij
    exact ⟨p i*s*(p j)⁻¹,⟨s,hs,rfl⟩⟩
  let B' := B.changeGraph (fun i j => (S' i j).Nonempty)
    (fun i j hij => hne i j (B.subgraph i j hij))
  let A' := A.changeGraph (fun i j => (S' j i).Nonempty)
    (fun i j hij => hne j i (A.subgraph i j hij))
  let inlabel : I → I → G := fun i j =>
    if h : A'.arc j i then (A'.subgraph j i h).choose else 1
  have hilabel : ∀ i j, A'.arc j i → inlabel i j ∈ S' i j := by
    intro i j h
    simp only [inlabel,dite_eq_left h]
    exact (A'.subgraph j i h).choose_spec
  obtain ⟨t,ht,hte⟩ := inward_tree_voltages A' inlabel
  refine ⟨p,hp.1,⟨⟨B',A',t,ht,hp.2,?_⟩⟩,gaugeLabels_stronglyConnected S p hsc⟩
  intro i j hij
  rw [hte i j hij,mul_inv_cancel_right]
  exact hilabel i j hij

end DirectedCycles
