module

public import DirectedCycles.TemplateEdgeCondition

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Tails of the selected cycle edges carrying the distinguished generator. -/
def Cycle.generatorTails {G : Type*} [Group G] {R : Digraph G} (C : Cycle R) (a : G) : Set G :=
  {x | ∃ i, C.vertex i = x ∧ C.vertex (finRotate C.length i) = x*a}

namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- Each explicit point belongs to the expanded cycle. -/
theorem expanded_point_mem {R : Digraph G} (E : ExpansionTemplate G I a l D)
    (C : Cycle R)
    (hV : List.ofFn C.vertex = (List.ofFn (fun e => List.ofFn (E.point e))).flatten)
    (e : Fin E.length) (k : Fin (E.pointCount e)) : E.point e k ∈ Set.range C.vertex := by
  have hv : E.point e k ∈ (List.ofFn (fun e => List.ofFn (E.point e))).flatten :=
    List.mem_flatten.mpr ⟨List.ofFn (E.point e),List.mem_ofFn.mpr ⟨e,rfl⟩,List.mem_ofFn.mpr ⟨k,rfl⟩⟩
  rw [← hV] at hv
  exact List.mem_ofFn.mp hv

theorem point_zero (E : ExpansionTemplate G I a l D) (e : Fin E.length) :
    E.point e ⟨0,E.pointCount_pos e⟩ = E.vertex e := by
  by_cases he : E.level e < l (E.position e)
  · simp only [point,he,ite_true]
  · simp only [point,he,ite_false,Nat.zero_le,ite_true,pow_zero,mul_one]

theorem expanded_retained_mem {R : Digraph G} (E : ExpansionTemplate G I a l D)
    (C : Cycle R)
    (hV : List.ofFn C.vertex = (List.ofFn (fun e => List.ofFn (E.point e))).flatten)
    (e : Fin E.length) : E.vertex e ∈ Set.range C.vertex := by
  rw [← E.point_zero e]
  exact E.expanded_point_mem C hV e ⟨0,E.pointCount_pos e⟩

/-- Every fixed-run auxiliary vertex is the tail of a selected expanded
cycle a-edge, including the edge into the connector's retained start. -/
theorem fixed_vertex_is_tail {R : Digraph G} (E : ExpansionTemplate G I a l D)
    (C : Cycle R)
    (hV : List.ofFn C.vertex = (List.ofFn (fun e => List.ofFn (E.point e))).flatten)
    (hA : C.ClosedUnderGenerator a) (e : Fin E.length)
    (he : E.level e < l (E.position e)) : E.vertex e ∈ C.generatorTails a := by
  obtain ⟨i,hi⟩ := E.expanded_retained_mem C hV e
  have hn : C.vertex i*a ∈ Set.range C.vertex := by
    rw [hi,← E.fixed_end e he]
    exact E.expanded_retained_mem C hV (finRotate E.length e)
  refine ⟨i,hi,?_⟩
  simpa only [hi] using hA i hn

end ExpansionTemplate
end DirectedCycles
