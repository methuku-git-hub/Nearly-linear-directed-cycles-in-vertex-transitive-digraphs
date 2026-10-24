import DirectedCycles.OrbitCyclePaths

set_option autoImplicit false
namespace DirectedCycles
namespace OrbitCycleWalk
variable {G I : Type*} [Group G] {S : I → I → Set G} {a : G}

def edgeLabel (W : OrbitCycleWalk (VoltageDigraph S) a) (i : Fin W.length) : G :=
  (W.point i.castSucc).1⁻¹*(W.point i.succ).1

theorem edgeLabel_mem (W : OrbitCycleWalk (VoltageDigraph S) a) (i : Fin W.length) :
    W.edgeLabel i ∈ S (W.orbitIndex i) (W.orbitIndex (finRotate W.length i)) := by
  obtain ⟨s,hs,he⟩ := W.step i
  rw [W.orbitIndex_succ i] at hs
  have hl : W.edgeLabel i = s := by
    simp only [edgeLabel,he,inv_mul_cancel_left]
  rw [hl]
  exact hs

/-- Choose one actual label on each nonempty orbit arc, retaining every
label of the prescribed orbit-cycle walk. Tail injectivity makes these
prescriptions consistent. -/
theorem exists_prescribed_labels (W : OrbitCycleWalk (VoltageDigraph S) a) :
    ∃ label : I → I → G,
      (∀ i j, (S i j).Nonempty → label i j ∈ S i j) ∧
      (∀ k, label (W.orbitIndex k) (W.orbitIndex (finRotate W.length k)) = W.edgeLabel k) := by
  classical
  let P := fun i j => ∃ k, W.orbitIndex k = i ∧ W.orbitIndex (finRotate W.length k) = j
  let label := fun i j => if h : P i j then W.edgeLabel h.choose
    else if h : (S i j).Nonempty then h.choose else 1
  refine ⟨label,?_,?_⟩
  · intro i j hij
    by_cases h : P i j
    · simp only [label,dite_eq_left h]
      have hs := W.edgeLabel_mem h.choose
      simpa only [h.choose_spec.1,h.choose_spec.2] using hs
    · simp only [label,dite_eq_right h,dite_eq_left hij]
      exact hij.choose_spec
  · intro k
    have h : P (W.orbitIndex k) (W.orbitIndex (finRotate W.length k)) := ⟨k,rfl,rfl⟩
    simp only [label,dite_eq_left h]
    exact congrArg W.edgeLabel (W.orbitIndex.injective h.choose_spec.1)

end OrbitCycleWalk
end DirectedCycles
