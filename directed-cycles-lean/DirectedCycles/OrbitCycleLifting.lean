module

public import DirectedCycles.OrbitCycleWalk
public import DirectedCycles.CayleyCycleLabels

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A simple cycle in the orbit digraph lifts to a walk with an explicit
endpoint voltage and a simple orbit projection. The initial coordinate is 1. -/
theorem voltage_orbit_cycle_walk {G I : Type*} [Group G]
    (S : I → I → Set G) (Q : Cycle (QuotientDigraph (VoltageDigraph S) Prod.snd)) :
    ∃ a : G, ∃ W : OrbitCycleWalk (VoltageDigraph S) a,
      W.length = Q.length ∧ (W.point 0).1 = 1 := by
  classical
  let : NeZero Q.length := ⟨by have := Q.two_le; omega⟩
  have hpos : 0 < Q.length := by have := Q.two_le; omega
  have hchoose : ∀ i, ∃ s ∈ S (Q.vertex i) (Q.vertex (finRotate Q.length i)), True := by
    intro i
    obtain ⟨_,x,y,hx,hy,a,ha,_⟩ := Q.arc i
    exact ⟨a,by simpa only [← hx,← hy] using ha,trivial⟩
  choose s hs _ using hchoose
  let index : Fin (Q.length+1) → Fin Q.length := fun j => ⟨j.val % Q.length,Nat.mod_lt _ hpos⟩
  let point : Fin (Q.length+1) → G × I := fun j => (((List.ofFn s).take j.val).prod,Q.vertex (index j))
  have hcast : ∀ i : Fin Q.length, index i.castSucc = i := by
    intro i
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  have hsucc : ∀ i : Fin Q.length, index i.succ = finRotate Q.length i := by
    intro i
    apply Fin.ext
    simp only [index,Fin.val_succ,finRotate_apply,Fin.val_add,Fin.val_one']
    rw [Nat.mod_eq_of_lt (show 1 < Q.length by have := Q.two_le; omega)]
  let a := (List.ofFn s).prod
  refine ⟨a,{
    length := Q.length
    two_le := Q.two_le
    point := point
    index_injective := ?_
    step := ?_
    closes := ?_
  },rfl,?_⟩
  · intro i j he
    change Q.vertex (index i.castSucc) = Q.vertex (index j.castSucc) at he
    rw [hcast,hcast] at he
    exact Q.vertex.injective he
  · intro i
    refine ⟨s i,?_,?_⟩
    · change s i ∈ S (Q.vertex (index i.castSucc)) (Q.vertex (index i.succ))
      rw [hcast,hsucc]
      exact hs i
    · exact ofFn_prefix_product_succ s i
  · change (((List.ofFn s).take Q.length).prod,Q.vertex (index (Fin.last Q.length))) =
      (a*((List.ofFn s).take 0).prod,Q.vertex (index 0))
    have ht : (List.ofFn s).take Q.length = List.ofFn s := List.take_of_length_le (by simp)
    rw [ht,List.take_zero,List.prod_nil,mul_one]
    apply Prod.ext
    · rfl
    · apply congrArg Q.vertex
      apply Fin.ext
      simp only [index,Fin.val_last,Fin.val_zero,Nat.mod_self,Nat.zero_mod]
  · change ((List.ofFn s).take 0).prod = 1
    simp only [List.take_zero,List.prod_nil]

end DirectedCycles
