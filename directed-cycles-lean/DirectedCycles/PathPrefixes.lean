module

public import DirectedCycles.Paths

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Truncate a simple path at any specified vertex, retaining both endpoints. -/
theorem prefix_through_vertex {V : Type*} {D : Digraph V} (P : List V)
    (hnd : P.Nodup) (hc : P.IsChain D) {x y : V}
    (hh : P.head? = some x) (hy : y ∈ P) :
    ∃ R : List V, R <+: P ∧ R ≠ [] ∧ R.Nodup ∧ R.IsChain D ∧
      R.head? = some x ∧ R.getLast? = some y := by
  obtain ⟨U,W,hP,_⟩ := List.eq_append_cons_of_mem hy
  let R := U ++ [y]
  have hp : R <+: P := ⟨W,by simpa only [R,List.append_assoc,List.singleton_append] using hP.symm⟩
  have hn : R ≠ [] := by simp [R]
  refine ⟨R,hp,hn,hnd.sublist hp.sublist,hc.prefix hp,?_,?_⟩
  · obtain ⟨L,hL⟩ := hp
    rw [← hL,List.head?_append_of_ne_nil _ hn] at hh
    exact hh
  · simp [R]

/-- The size of a list enumerating a subgroup exactly once. -/
theorem subgroup_enumeration_length {G : Type*} [Group G] (H : Subgroup G) (P : List G)
    (hnd : P.Nodup) (hm : ∀ x, x ∈ P ↔ x ∈ H) : P.length = Nat.card H := by
  let f : Fin P.length → H := fun i => ⟨P.get i,(hm _).mp (List.get_mem _ _)⟩
  have hi : Function.Injective f := by
    intro i j he
    exact List.nodup_iff_injective_get.mp hnd (congrArg Subtype.val he)
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((hm x.val).mpr x.property)
    exact ⟨i,Subtype.ext hi⟩
  simpa only [Nat.card_fin] using Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)

end DirectedCycles
