import DirectedCycles.DifferenceConstraints

set_option autoImplicit false
namespace DirectedCycles

/-- A family that has at most one outgoing and one incoming constraint
per tag has at most twice as many incident constraints as tags. -/
theorem tagged_incidence_degree {I C K : Type*} [Fintype C] [Fintype K] [DecidableEq I]
    (src dst : C → I) (tag : C → K)
    (hs : Function.Injective (fun c => (tag c,src c)))
    (ht : Function.Injective (fun c => (tag c,dst c))) (i : I) :
    (Finset.univ.filter (fun c => src c = i ∨ dst c = i)).card ≤ 2*Fintype.card K := by
  classical
  let U := Finset.univ.filter (fun c => src c = i ∨ dst c = i)
  let f : U → K ⊕ K := fun c => if src c.val = i then Sum.inl (tag c.val) else Sum.inr (tag c.val)
  have hi : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    have hc := (Finset.mem_filter.mp c.property).2
    have hd := (Finset.mem_filter.mp d.property).2
    by_cases hcs : src c.val = i
    · by_cases hds : src d.val = i
      · apply hs
        exact Prod.ext (by simpa only [f,ite_eq_left hcs,ite_eq_left hds,Sum.inl.injEq] using he)
          (hcs.trans hds.symm)
      · simp only [f,ite_eq_left hcs,ite_eq_right hds,Sum.inl_ne_inr] at he
    · by_cases hds : src d.val = i
      · simp only [f,ite_eq_right hcs,ite_eq_left hds,Sum.inr_ne_inl] at he
      · apply ht
        exact Prod.ext (by simpa only [f,ite_eq_right hcs,ite_eq_right hds,Sum.inr.injEq] using he)
          ((hc.resolve_left hcs).trans (hd.resolve_left hds).symm)
  have hh := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,Fintype.card_sum,two_mul] using hh

/-- The actual collision constraints induced by right multiplication
between two injective lists of quotient positions. -/
def RightCollision {I K H : Type*} [Group H] (start finish : I ↪ H) (label : K → H) :=
  {p : K × I × I // start p.2.1 * label p.1 = finish p.2.2 ∧ p.2.1 ≠ p.2.2}

instance {I K H : Type*} [Group H] [Finite I] [Finite K]
    (start finish : I ↪ H) (label : K → H) : Finite (RightCollision start finish label) :=
  inferInstanceAs (Finite {_p : K × I × I // _})

theorem right_collision_degree {I K H : Type*} [Group H] [Fintype I] [Fintype K]
    [DecidableEq I] (start finish : I ↪ H) (label : K → H) :
    let C := RightCollision start finish label
    ∀ [Fintype C] (i : I),
      (Finset.univ.filter (fun c : C => c.val.2.1 = i ∨ c.val.2.2 = i)).card ≤ 2*Fintype.card K := by
  intro C _ i
  apply tagged_incidence_degree (fun c : C => c.val.2.1) (fun c : C => c.val.2.2)
    (fun c : C => c.val.1)
  · intro c d he
    have hk := congrArg (fun z : K × I => z.1) he
    have hi := congrArg (fun z : K × I => z.2) he
    change c.val.1 = d.val.1 at hk
    change c.val.2.1 = d.val.2.1 at hi
    have hj : c.val.2.2 = d.val.2.2 := by
      apply finish.injective
      rw [← c.property.1,← d.property.1,hk,hi]
    exact Subtype.ext (Prod.ext hk (Prod.ext hi hj))
  · intro c d he
    have hk := congrArg (fun z : K × I => z.1) he
    have hj := congrArg (fun z : K × I => z.2) he
    change c.val.1 = d.val.1 at hk
    change c.val.2.2 = d.val.2.2 at hj
    have hi : c.val.2.1 = d.val.2.1 := by
      apply start.injective
      apply mul_right_cancel (b := label c.val.1)
      rw [c.property.1,hj,hk,d.property.1]
    exact Subtype.ext (Prod.ext hk (Prod.ext hi hj))

end DirectedCycles
