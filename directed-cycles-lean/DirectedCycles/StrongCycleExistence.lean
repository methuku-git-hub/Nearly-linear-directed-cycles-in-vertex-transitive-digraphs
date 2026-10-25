module

public import DirectedCycles.Paths

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A nonloop arc and a return walk contain a simple directed cycle. -/
theorem cycle_of_arc_and_return {V : Type*} {D : Digraph V} {x y : V}
    (hxy : D x y) (hne : x ≠ y) (hr : Reachable D y x) : Nonempty (Cycle D) := by
  classical
  obtain ⟨P⟩ := simplePath_of_reachable hr
  have hPne := P.dropLast_nonempty hne.symm
  have hPword : P.vertices.dropLast ++ [x] = P.vertices :=
    List.dropLast_append_getLast? x P.last
  have hxnot : x ∉ P.vertices.dropLast := by
    have h := P.nodup
    rw [← hPword,List.nodup_append] at h
    intro hx
    exact h.2.2 x hx x (by simp) rfl
  let L := x :: P.vertices.dropLast
  have hnd : L.Nodup := List.nodup_cons.mpr ⟨hxnot,P.nodup.sublist (List.dropLast_sublist _)⟩
  have hlen : 2 ≤ L.length := by
    have := List.length_pos_iff.mpr hPne
    simp only [L,List.length_cons]
    omega
  have hc : CircularChain D L := by
    constructor
    · apply List.isChain_cons.mpr
      refine ⟨?_,P.chain.dropLast⟩
      intro z hz
      have hz' : z = y := by
        simpa only [P.dropLast_head hne.symm,P.head,Option.mem_some_iff,eq_comm] using hz
      exact hz' ▸ hxy
    · intro u hu v hv
      have hv' : v = x := by simpa only [L,List.head?_cons,Option.mem_some_iff,eq_comm] using hv
      subst v
      have hu' : u ∈ P.vertices.dropLast.getLast? := by
        simpa only [L,List.getLast?_cons_of_ne_nil hPne] using hu
      exact P.dropLast_last_arc u hu'
  exact ⟨cycleOfList L hnd hlen hc⟩

/-- Strong connectivity on a nontrivial vertex set supplies a nonloop arc. -/
theorem stronglyConnected_nonloop_arc {V : Type*} [Nontrivial V] {D : Digraph V}
    (h : StronglyConnected D) : ∃ x y, D x y ∧ x ≠ y := by
  obtain ⟨x,y,hxy⟩ := exists_pair_ne V
  by_contra he
  have hall : ∀ x y, D x y → x = y := by
    intro u v huv
    by_contra hne
    exact he ⟨u,v,huv,hne⟩
  have heq : ∀ {u v}, Reachable D u v → u = v := by
    intro u v hr
    induction hr with
    | refl => rfl
    | tail hr huv ih => exact ih.trans (hall _ _ huv)
  exact hxy (heq (h x y))

theorem stronglyConnected_cycle {V : Type*} [Nontrivial V] {D : Digraph V}
    (h : StronglyConnected D) : Nonempty (Cycle D) := by
  obtain ⟨x,y,hxy,hne⟩ := stronglyConnected_nonloop_arc h
  exact cycle_of_arc_and_return hxy hne (h y x)

end DirectedCycles
