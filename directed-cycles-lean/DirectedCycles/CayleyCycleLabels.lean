import DirectedCycles.CayleyWords

set_option autoImplicit false
namespace DirectedCycles

/-- The finite prefix products of a list of chosen labels have the exact
successive multiplication rule. -/
theorem ofFn_prefix_product_succ {G : Type*} [Group G] {n : ℕ}
    (s : Fin n → G) (i : Fin n) :
    ((List.ofFn s).take (i.val+1)).prod = ((List.ofFn s).take i.val).prod*s i := by
  rw [← List.take_concat_get' (List.ofFn s) i.val (by simpa only [List.length_ofFn] using i.isLt),
    List.prod_append,List.prod_singleton,List.getElem_ofFn]

/-- Any cycle in an image Cayley graph has original generator labels for its
arcs. These are chosen from S itself. -/
theorem cayley_cycle_labels {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (S : Set G) (C : Cycle (CayleyDigraph (q '' S))) :
    ∃ s : Fin C.length → G, (∀ i, s i ∈ S) ∧
      ∀ i, C.vertex (finRotate C.length i) = C.vertex i*q (s i) := by
  have h : ∀ i, ∃ s ∈ S, C.vertex (finRotate C.length i) = C.vertex i*q s := by
    intro i
    obtain ⟨b,⟨s,hs,rfl⟩,hb⟩ := C.arc i
    exact ⟨s,hs,hb⟩
  choose s hs he using h
  exact ⟨s,hs,he⟩

/-- Chosen cycle labels have prefix products equal to the translated cycle
vertices, with the identity as first vertex. -/
theorem cayley_cycle_prefixes {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (S : Set Q) (C : Cycle (CayleyDigraph S)) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*q (s i)) :
    ∀ i : Fin C.length, q ((List.ofFn s).take i.val).prod =
      (C.vertex ⟨0,by have := C.two_le; omega⟩)⁻¹*C.vertex i := by
  let : NeZero C.length := ⟨by have := C.two_le; omega⟩
  have hp : ∀ n, ∀ hn : n < C.length, q ((List.ofFn s).take n).prod =
      (C.vertex ⟨0,by have := C.two_le; omega⟩)⁻¹*C.vertex ⟨n,hn⟩ := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      have hn0 : n < C.length := by omega
      have hrot : finRotate C.length ⟨n,hn0⟩ = ⟨n+1,hn⟩ := by
        apply Fin.ext
        rw [finRotate_apply]
        simp only [Fin.val_add,Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < C.length by have := C.two_le; omega),Nat.mod_eq_of_lt hn]
      have hpstep := ofFn_prefix_product_succ s ⟨n,hn0⟩
      change ((List.ofFn s).take (n+1)).prod = ((List.ofFn s).take n).prod*s ⟨n,hn0⟩ at hpstep
      rw [hpstep,map_mul,ih hn0,mul_assoc,← hstep ⟨n,hn0⟩,hrot]
  exact fun i => hp i.val i.isLt

/-- The full label word closes in the quotient, even if its lift in G does
not close. -/
theorem cayley_cycle_word_closes {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (S : Set Q) (C : Cycle (CayleyDigraph S)) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*q (s i)) :
    q (List.ofFn s).prod = 1 := by
  let last : Fin C.length := ⟨C.length-1,by have := C.two_le; omega⟩
  have hlast : last.val+1 = C.length := by dsimp [last]; have := C.two_le; omega
  have hrot : finRotate C.length last = ⟨0,by have := C.two_le; omega⟩ := by
    apply Fin.ext
    let : NeZero C.length := ⟨by have := C.two_le; omega⟩
    rw [finRotate_apply]
    simp only [Fin.val_add,Fin.val_one']
    rw [Nat.mod_eq_of_lt (show 1 < C.length by have := C.two_le; omega),hlast,Nat.mod_self]
  have hp := congrArg q (ofFn_prefix_product_succ s last)
  have ht : (List.ofFn s).take C.length = List.ofFn s := List.take_of_length_le (by simp)
  rw [hlast,ht] at hp
  rw [map_mul,cayley_cycle_prefixes q S C s hstep, mul_assoc,← hstep last,hrot,inv_mul_cancel] at hp
  exact hp

end DirectedCycles
