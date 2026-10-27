module

public import DirectedCycles.TemplateNoShortcut
public import DirectedCycles.ConnectorNonAStep
public import DirectedCycles.WordSteps
public import DirectedCycles.TemplateCycleRelation

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The distinguished-generator successor belongs to the cycle whenever both
endpoints do. This describes the selected cycle edges, not merely graph arcs. -/
def Cycle.ClosedUnderGenerator {G : Type*} [Group G] {R : Digraph G} (C : Cycle R) (a : G) : Prop :=
  ∀ i, C.vertex i*a ∈ Set.range C.vertex → C.vertex (finRotate C.length i) = C.vertex i*a

namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- Preserve the successor constraint as part of the relation checked along
all word paths. -/
theorem constrained_word_chains {Q : Type*} [Group Q]
    (E : ExpansionTemplate G I a l D) (q : G →* Q) (h : ℕ)
    (hgap : ∀ i, l i+2*D+2 ≤ h) (hpow : (q a)^h = 1) (r : I → Q)
    (hcoord : Function.Injective (fun z : I × Fin h => r z.1*(q a)^z.2.val))
    (hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e))
    (S : Set G) (ha : a ∈ S) (hs : ∀ e, E.label e ∈ S) :
    ∀ e, (wordVertices (E.vertex e) (E.edgeWord e)).IsChain
      (fun x y => CayleyDigraph S x y ∧ ((∃ f k, E.point f k = x*a) → y = x*a)) := by
  intro e
  apply wordVertices_chain_of_steps
  intro i
  refine ⟨⟨(E.edgeWord e)[i.val],E.edgeWord_allowed S ha hs e _ (List.getElem_mem i.isLt),rfl⟩,?_⟩
  intro hmem
  by_cases hstep : (E.edgeWord e)[i.val] = a
  · rw [hstep]
  · obtain ⟨he,hprefix⟩ := E.edgeWord_non_a_step e i hstep
    obtain ⟨f,k,hfk⟩ := hmem
    rw [hprefix] at hfk
    exact (E.connector_successor_absent q h hgap hpow r hcoord hx e he f k hfk).elim

/-- The expanded simple cycle has the full distinguished-generator edge
condition. Its vertex list is still exactly the explicit word expansion. -/
theorem simple_cycle_with_edge_condition {Q : Type*} [Group Q]
    (E : ExpansionTemplate G I a l D) (q : G →* Q) (h : ℕ)
    (hgap : ∀ i, l i+2*D+2 ≤ h) (hpow : (q a)^h = 1) (r : I → Q)
    (hcoord : Function.Injective (fun z : I × Fin h => r z.1*(q a)^z.2.val))
    (hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e))
    (S : Set G) (ha : a ∈ S) (hs : ∀ e, E.label e ∈ S) :
    ∃ C : Cycle (CayleyDigraph S), C.length = ∑ e, E.pointCount e ∧ E.length ≤ C.length ∧
      List.ofFn C.vertex = (List.ofFn (fun e => List.ofFn (E.point e))).flatten ∧
      C.ClosedUnderGenerator a := by
  let R : Digraph G := fun x y => CayleyDigraph S x y ∧ ((∃ f k, E.point f k = x*a) → y = x*a)
  obtain ⟨C,hC,hL,hV⟩ := E.cycle_of_word_chains q h hgap hpow r hcoord hx R
    (E.constrained_word_chains q h hgap hpow r hcoord hx S ha hs)
  let C' := C.map (Function.Embedding.refl G) (fun _ _ hh => hh.1)
  refine ⟨C',hC,hL,hV,?_⟩
  intro i hi
  obtain ⟨j,hj⟩ := hi
  have hv := E.expanded_vertex_mem C hV j
  apply (C.arc i).2
  obtain ⟨e,k,hk⟩ := hv
  exact ⟨e,k,hk.trans hj⟩

end ExpansionTemplate
end DirectedCycles
