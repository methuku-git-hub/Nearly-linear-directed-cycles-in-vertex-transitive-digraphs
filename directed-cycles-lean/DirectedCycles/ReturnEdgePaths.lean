module

public import DirectedCycles.TranslatedReturnPaths
public import DirectedCycles.ReturnCycleExpansion

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

def SimplePath.changeLast {V : Type*} {D : Digraph V} {x y : V}
    (P : SimplePath D x y) (z : V) (hy : y = z) : SimplePath D x z where
  vertices := P.vertices
  nodup := P.nodup
  head := P.head
  last := P.last.trans (congrArg some hy)
  chain := P.chain

/-- Assemble the a-paths and connector paths along a Cayley cycle.
Only the distinct-connector geometric disjointness remains an input;
the final walk-expansion conditions are proved here. -/
theorem cycle_of_return_edge_paths {G I K : Type*} [Group G] {R : Digraph G}
    (S : I → I → Set G) (root : I) (a : G) (C : Cycle R) (hclosed : C.ClosedUnderGenerator a)
    (t : I → G) (htroot : t root = 1) (Q₀ : Set I) (ht : ∀ z ∈ Q₀, z ≠ root → t z = a)
    (A : SimplePath (VoltageDigraph S) (1,root) (a,root))
    (hA : ∀ x z, z ∈ (A.translateRoot x).vertices.dropLast → z.1 = x ∧ z.2 ∈ Q₀)
    (label : K → G) (P : ∀ k, SimplePath (VoltageDigraph S) (1,root) (label k,root))
    (hP : ∀ k z, z ∈ (P k).vertices → z.1 = 1 ∨ z.1 = label k*(t z.2)⁻¹)
    (pick : ∀ e : Fin C.length, C.vertex (finRotate C.length e) ≠ C.vertex e*a → K)
    (hend : ∀ e h, C.vertex (finRotate C.length e) = C.vertex e*label (pick e h))
    (hdisjoint : ∀ i j, i ≠ j →
      ∀ hi : C.vertex (finRotate C.length i) ≠ C.vertex i*a,
      ∀ hj : C.vertex (finRotate C.length j) ≠ C.vertex j*a,
      ((P (pick i hi)).translateRoot (C.vertex i)).vertices.Disjoint
        ((P (pick j hj)).translateRoot (C.vertex j)).vertices) :
    ∃ L : Cycle (VoltageDigraph S), C.length ≤ L.length := by
  classical
  let isA := fun e : Fin C.length => C.vertex (finRotate C.length e) = C.vertex e*a
  let paths := fun e : Fin C.length =>
    if h : isA e then
      (A.translateRoot (C.vertex e)).changeLast (C.vertex (finRotate C.length e),root)
        (Prod.ext h.symm rfl)
    else
      ((P (pick e h)).translateRoot (C.vertex e)).changeLast
        (C.vertex (finRotate C.length e),root) (Prod.ext (hend e h).symm rfl)
  apply return_cycle_expansion S root a C hclosed t Q₀ ht isA paths
  · intro e z hz hr
    by_cases he : isA e
    · simp only [paths,dite_eq_left he,SimplePath.changeLast] at hz
      exact (hA (C.vertex e) z hz).1
    · simp only [paths,dite_eq_right he,SimplePath.changeLast] at hz
      have hh := (P (pick e he)).translated_root_occurrence t htroot (hP _) (C.vertex e) z hz hr
      exact congrArg Prod.fst hh
  · intro e he z hz
    simp only [paths,dite_eq_left he,SimplePath.changeLast] at hz
    exact hA (C.vertex e) z hz
  · intro e he z hz
    simp only [paths,dite_eq_right he,SimplePath.changeLast] at hz
    have hh := (P (pick e he)).translated_occurrence t (hP _) (C.vertex e) z
      (List.mem_of_mem_dropLast hz)
    simpa only [← hend e he] using hh
  · intro i j hij hi hj
    simpa only [paths,dite_eq_right hi,dite_eq_right hj,SimplePath.changeLast] using hdisjoint i j hij hi hj

end DirectedCycles
