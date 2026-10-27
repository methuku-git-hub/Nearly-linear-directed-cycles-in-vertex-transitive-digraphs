module

public import DirectedCycles.PrescribedReturnVoltages
public import DirectedCycles.ReturnSpineExistence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace OrbitCycleWalk
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I] {S : I → I → Set G} {a : G}

/-- The return-tree system can be chosen compatibly with the prescribed
orbit cycle. At every nonroot orbit of that cycle the return voltage is a. -/
theorem exists_prescribed_return_spine (W : OrbitCycleWalk (VoltageDigraph S) a)
    (hstart : (W.point 0).1 = 1) (hsc : StronglyConnected (VoltageDigraph S)) :
    ∃ p : I → G, p (W.point 0).2 = 1 ∧
      ∃ R : ReturnSpine (gaugeLabels S p) (W.point 0).2,
        (∀ k : Fin W.length, 0 < k.val → R.voltage (W.orbitIndex k) = a) ∧
        (∀ k : Fin W.length, p (W.orbitIndex k) = (W.point k.castSucc).1) ∧
        StronglyConnected (VoltageDigraph (gaugeLabels S p)) := by
  classical
  let D : Digraph I := fun i j => (S i j).Nonempty
  have hD : StronglyConnected D := by
    intro i j
    exact reachable_map Prod.snd (fun _ _ h => by obtain ⟨s,hs,_⟩ := h; exact ⟨s,hs⟩)
      (hsc (1,i) (1,j))
  obtain ⟨B,A,hB,hA⟩ := branchings_containing_paths W.outOrbitPath W.inOrbitPath hD
  obtain ⟨label,hlabel,hprescribed⟩ := W.exists_prescribed_labels
  let p := fun i => B.potential label i (Finset.mem_univ i)
  have hp := gauge_outward_tree B S label (fun i j hij => hlabel i j (B.subgraph i j hij))
  change p (W.point 0).2 = 1 ∧ ∀ x y, B.arc x y → 1 ∈ gaugeLabels S p x y at hp
  have hpot := W.out_tree_potential hstart B hB label hprescribed
  change ∀ k, p (W.orbitIndex k) = (W.point k.castSucc).1 at hpot
  let S' := gaugeLabels S p
  have hne : ∀ i j, D i j → (S' i j).Nonempty := by
    intro i j hij
    obtain ⟨s,hs⟩ := hij
    exact ⟨p i*s*(p j)⁻¹,⟨s,hs,rfl⟩⟩
  let B' := B.changeGraph (fun i j => (S' i j).Nonempty)
    (fun i j hij => hne i j (B.subgraph i j hij))
  let A' := A.changeGraph (fun i j => (S' j i).Nonempty)
    (fun i j hij => hne j i (A.subgraph i j hij))
  let inlabel := fun i j => p i*label i j*(p j)⁻¹
  have hilabel : ∀ i j, A'.arc j i → inlabel i j ∈ S' i j := by
    intro i j hij
    exact ⟨label i j,hlabel i j (A.subgraph j i hij),rfl⟩
  obtain ⟨t,ht,hte⟩ := inward_tree_voltages A' inlabel
  let R : ReturnSpine S' (W.point 0).2 := {
    out := B'
    inward := A'
    voltage := t
    root_voltage := ht
    out_label := hp.2
    in_label := by
      intro i j hij
      rw [hte i j hij,mul_inv_cancel_right]
      exact hilabel i j hij
  }
  refine ⟨p,hp.1,R,?_,hpot,gaugeLabels_stronglyConnected S p hsc⟩
  exact W.inward_cycle_voltages A.arc hA inlabel t ht hte
    (W.normalized_cycle_labels p hpot label hprescribed)

end OrbitCycleWalk
end DirectedCycles
