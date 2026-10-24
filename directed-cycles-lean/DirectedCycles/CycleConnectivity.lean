import DirectedCycles.Basic

set_option autoImplicit false
namespace DirectedCycles

theorem finRotate_stronglyConnected (n : ℕ) (hn : 0 < n) :
    StronglyConnected (fun i j : Fin n => j = finRotate n i) := by
  let : NeZero n := ⟨hn.ne'⟩
  intro i j
  have hiter : ∀ k : ℕ, Reachable (fun a b : Fin n => b = finRotate n a) i ((finRotate n)^[k] i) := by
    intro k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail rfl
  have he : (finRotate n)^[(j-i).val] i = j := by
    rw [← finCycle_eq_finRotate_iterate,finCycle_apply]
    abel
  rw [← he]
  exact hiter _

/-- A cycle contained in one fibre and covering it makes that induced
fibre strongly connected. -/
theorem cycle_fibre_stronglyConnected {V W : Type*} {D : Digraph V} (C : Cycle D)
    (pi : V → W) (w : W) (hmem : ∀ i, pi (C.vertex i) = w)
    (hcover : ∀ x, pi x = w → ∃ i, C.vertex i = x) :
    StronglyConnected (fun x y : {v // pi v = w} => D x.val y.val) := by
  let f : Fin C.length → {v // pi v = w} := fun i => ⟨C.vertex i,hmem i⟩
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨i,hi⟩ := hcover x.val x.property
    exact ⟨i,Subtype.ext hi⟩
  apply stronglyConnected_image f hs
    (fun i j (h : j = finRotate C.length i) => h ▸ C.arc i)
    (finRotate_stronglyConnected C.length (by have := C.two_le; omega))

end DirectedCycles
