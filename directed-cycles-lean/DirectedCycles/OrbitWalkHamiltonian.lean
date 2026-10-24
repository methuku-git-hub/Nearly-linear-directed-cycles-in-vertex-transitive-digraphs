import DirectedCycles.CayleyCycleLabels
import DirectedCycles.OrbitCycleLabels
import DirectedCycles.BaselineHamiltonian

set_option autoImplicit false
namespace DirectedCycles
namespace OrbitCycleWalk
variable {G I : Type*} [Group G] {S : I → I → Set G} {a : G}

/-- Multiplying the actual labels telescopes to the endpoint voltage. -/
theorem label_product (W : OrbitCycleWalk (VoltageDigraph S) a) (hstart : (W.point 0).1 = 1) :
    (List.ofFn W.edgeLabel).prod = a := by
  have hp : ∀ k : ℕ, ∀ hk : k ≤ W.length,
      ((List.ofFn W.edgeLabel).take k).prod = (W.point ⟨k,by omega⟩).1 := by
    intro k
    induction k with
    | zero => intro hk; simpa using hstart.symm
    | succ k ih =>
      intro hk
      have hk' : k < W.length := by omega
      have hs := ofFn_prefix_product_succ W.edgeLabel ⟨k,hk'⟩
      change ((List.ofFn W.edgeLabel).take (k+1)).prod =
        ((List.ofFn W.edgeLabel).take k).prod*W.edgeLabel ⟨k,hk'⟩ at hs
      rw [hs,ih (by omega)]
      simp only [edgeLabel]
      exact mul_inv_cancel_left _ _
  have hh := hp W.length le_rfl
  rw [List.take_of_length_le (by simp)] at hh
  change (List.ofFn W.edgeLabel).prod = (W.point (Fin.last W.length)).1 at hh
  rw [W.closes,hstart,mul_one] at hh
  exact hh

/-- If the orbit-cycle voltage generates the group, repeating its label
round gives a simple cycle covering every vertex in those orbits. -/
theorem generating_voltage_cycle [Finite G] (W : OrbitCycleWalk (VoltageDigraph S) a)
    (hstart : (W.point 0).1 = 1) (hgen : Subgroup.zpowers a = ⊤) :
    ∃ C : Cycle (VoltageDigraph S), C.length = W.length*Nat.card G := by
  classical
  let : NeZero W.length := ⟨by have := W.two_le; omega⟩
  let : Fact (1 < W.length) := ⟨by have := W.two_le; omega⟩
  let index : ZMod W.length → Fin W.length := fun z => ⟨z.val,ZMod.val_lt z⟩
  have hindex : Function.Injective index := by
    intro x y he
    apply ZMod.val_injective W.length
    exact congrArg Fin.val he
  have hnext : ∀ z : ZMod W.length, index (z+1) = finRotate W.length (index z) := by
    intro z
    apply Fin.ext
    change (z+1).val = (finRotate W.length (index z)).val
    rw [finRotate_apply]
    simp only [Fin.val_add,Fin.val_one']
    rw [ZMod.val_add,ZMod.val_one, Nat.mod_eq_of_lt (show 1 < W.length by have := W.two_le; omega)]
  let B : ZMod W.length → Set G := fun z => {W.edgeLabel (index z)}
  let xs := List.ofFn W.edgeLabel
  have hword : LayerWord B 0 xs := by
    apply (layerWord_iff_get B 0 xs).mpr
    intro j
    have hj : j.val < W.length := by simpa only [xs,List.length_ofFn] using j.isLt
    change xs[j.val] = W.edgeLabel (index (0+(j.val : ZMod W.length)))
    simp only [xs,List.getElem_ofFn,zero_add,index,ZMod.val_natCast_of_lt hj]
  obtain ⟨C,hC,_⟩ := generating_baseline_hamiltonian B xs List.length_ofFn hword
    (by simpa only [xs,W.label_product hstart] using hgen)
  let f : G × ZMod W.length ↪ G × I := {
    toFun x := (x.1,W.orbitIndex (index x.2))
    inj' := by
      intro x y he
      have he2 := congrArg (fun z : G × I => z.2) he
      have he1 := congrArg (fun z : G × I => z.1) he
      have hi : index x.2 = index y.2 := W.orbitIndex.injective he2
      exact Prod.ext he1 (hindex hi)
  }
  have hf : ∀ x y, CyclicLayerDigraph B x y → VoltageDigraph S (f x) (f y) := by
    rintro x y ⟨hy,s,hs,he⟩
    have hs' : s = W.edgeLabel (index x.2) := hs
    refine ⟨s,?_,he⟩
    change s ∈ S (W.orbitIndex (index x.2)) (W.orbitIndex (index y.2))
    rw [hs',hy,hnext]
    exact W.edgeLabel_mem _
  exact ⟨C.map f hf,hC⟩

end OrbitCycleWalk
end DirectedCycles
