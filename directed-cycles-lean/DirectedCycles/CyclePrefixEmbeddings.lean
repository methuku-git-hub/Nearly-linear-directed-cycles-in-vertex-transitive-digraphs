module

public import DirectedCycles.CayleyCycleLabels

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem cayley_cycle_target_prefixes {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (S : Set Q) (C : Cycle (CayleyDigraph S)) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*q (s i)) (i : Fin C.length) :
    q ((List.ofFn s).take (i.val+1)).prod =
      (C.vertex ⟨0,by have := C.two_le; omega⟩)⁻¹*C.vertex (finRotate C.length i) := by
  rw [ofFn_prefix_product_succ s i,map_mul,cayley_cycle_prefixes q S C s hstep,mul_assoc,← hstep i]

def cycleSourceEmbedding {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (S : Set Q) (C : Cycle (CayleyDigraph S)) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*q (s i)) : Fin C.length ↪ Q :=
  ⟨fun i => q ((List.ofFn s).take i.val).prod,by
    intro i j he
    simp only [cayley_cycle_prefixes q S C s hstep] at he
    exact C.vertex.injective (mul_left_cancel he)⟩

def cycleTargetEmbedding {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (S : Set Q) (C : Cycle (CayleyDigraph S)) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*q (s i)) : Fin C.length ↪ Q :=
  ⟨fun i => q ((List.ofFn s).take (i.val+1)).prod,by
    intro i j he
    simp only [cayley_cycle_target_prefixes q S C s hstep] at he
    exact (finRotate C.length).injective (C.vertex.injective (mul_left_cancel he))⟩

end DirectedCycles
