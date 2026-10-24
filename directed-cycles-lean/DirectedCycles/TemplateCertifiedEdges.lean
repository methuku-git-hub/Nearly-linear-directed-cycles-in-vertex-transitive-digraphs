import DirectedCycles.TemplateEdgeCondition

set_option autoImplicit false
namespace DirectedCycles
namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- Expansion preserves any additional edge predicate while retaining
the distinguished-generator successor condition. -/
theorem simple_cycle_with_edge_data {Q : Type*} [Group Q]
    (E : ExpansionTemplate G I a l D) (q : G →* Q) (h : ℕ)
    (hgap : ∀ i, l i+2*D+2 ≤ h) (hpow : (q a)^h = 1) (r : I → Q)
    (hcoord : Function.Injective (fun z : I × Fin h => r z.1*(q a)^z.2.val))
    (hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e))
    (S : Set G) (ha : a ∈ S) (hs : ∀ e, E.label e ∈ S)
    (R : Digraph G) (hR : ∀ e, (wordVertices (E.vertex e) (E.edgeWord e)).IsChain R) :
    ∃ C : Cycle (CayleyDigraph S), E.length ≤ C.length ∧ C.ClosedUnderGenerator a ∧
      (∀ i, R (C.vertex i) (C.vertex (finRotate C.length i))) := by
  let A : Digraph G := fun x y =>
    (CayleyDigraph S x y ∧ ((∃ f k, E.point f k = x*a) → y = x*a)) ∧ R x y
  have hchains : ∀ e, (wordVertices (E.vertex e) (E.edgeWord e)).IsChain A := by
    intro e
    have h₁ := E.constrained_word_chains q h hgap hpow r hcoord hx S ha hs e
    have h₂ := hR e
    apply List.isChain_iff_getElem.mpr
    intro i hi
    exact ⟨h₁.getElem i hi,h₂.getElem i hi⟩
  obtain ⟨C,_,hL,hV⟩ := E.cycle_of_word_chains q h hgap hpow r hcoord hx A hchains
  let C' := C.map (Function.Embedding.refl G) (fun _ _ hh => hh.1.1)
  refine ⟨C',hL,?_,fun i => (C.arc i).2⟩
  intro i hi
  obtain ⟨j,hj⟩ := hi
  obtain ⟨e,k,hk⟩ := E.expanded_vertex_mem C hV j
  exact (C.arc i).1.2 ⟨e,k,hk.trans hj⟩

theorem edgeWord_non_a_label (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (i : Fin (E.edgeWord e).length) (hi : (E.edgeWord e)[i.val] ≠ a) :
    (E.edgeWord e)[i.val] = E.label e := by
  have he := (E.edgeWord_non_a_step e i hi).1
  have hn : ¬ E.level e < l (E.position e) := by omega
  have hw : E.edgeWord e = List.replicate (E.choice e).val a ++ [E.label e] ++
      List.replicate (D-(E.choice e).val) a := by simp only [edgeWord,hn,ite_false]
  have hi' : i.val < (List.replicate (E.choice e).val a ++ [E.label e] ++
      List.replicate (D-(E.choice e).val) a).length := by simpa only [← hw] using i.isLt
  have hne : (List.replicate (E.choice e).val a ++ [E.label e] ++
      List.replicate (D-(E.choice e).val) a)[i.val] ≠ a := by simpa only [← hw] using hi
  have hik := (connector_non_a_step a (E.label e) (E.choice e).val
    (D-(E.choice e).val) i.val hi' hne).1
  simp only [hw,hik]
  rw [List.getElem_append_left (by simp),List.getElem_append_right (by simp)]
  simp only [List.length_replicate,Nat.sub_self,List.getElem_cons_zero]

def allowedStep (E : ExpansionTemplate G I a l D) : Digraph G := fun x y =>
  y = x*a ∨ ∃ e, E.level e = l (E.position e) ∧
    x = E.vertex e*a^(E.choice e).val ∧ y = x*E.label e

theorem allowedStep_word_chains (E : ExpansionTemplate G I a l D) :
    ∀ e, (wordVertices (E.vertex e) (E.edgeWord e)).IsChain E.allowedStep := by
  intro e
  apply wordVertices_chain_of_steps
  intro i
  by_cases hi : (E.edgeWord e)[i.val] = a
  · exact Or.inl (by rw [hi])
  · obtain ⟨he,hprefix⟩ := E.edgeWord_non_a_step e i hi
    exact Or.inr ⟨e,he,by rw [hprefix],by rw [E.edgeWord_non_a_label e i hi]⟩

end ExpansionTemplate
end DirectedCycles
