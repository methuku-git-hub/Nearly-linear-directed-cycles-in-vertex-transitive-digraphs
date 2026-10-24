import DirectedCycles.ActualFixedFibres
import DirectedCycles.FullCosetSpanning
import DirectedCycles.ConsecutiveNormalFibres

set_option autoImplicit false
namespace DirectedCycles

/-- The actual expanded a-edge tails span A_D(G) from the manuscript's
quotient spanning and per-layer B-coordinate spanning hypotheses. -/
theorem actual_expanded_tails_span {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hC : cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a)
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hl : ∀ i : Fin data.length, (data[i.val]).1 < orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (hD : ∀ i : Fin data.length, D ≤ (data[i.val]).1)
    (Q : Cycle (cyclicAuxiliaryGraph a D data hne))
    (hquot : SpansTruncation D (Set.range (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc))))
    (hlayer : ∀ z, SpansTruncation D (auxiliaryLayerCoordinates a D data hne Q z))
    (R : Digraph G) (L : Cycle R)
    (hV : let E := cyclicAuxiliary_expansionTemplate a D data hne hC hr hl Q
      List.ofFn L.vertex = (List.ofFn (fun e => List.ofFn (E.point e))).flatten)
    (hA : L.ClosedUnderGenerator a) : SpansTruncation D (L.generatorTails a) := by
  let W := AddSubgroup.closure (truncatedElement G D '' L.generatorTails a)
  have hW : ∀ x ∈ L.generatorTails a, truncatedElement G D x ∈ W :=
    fun x hx => AddSubgroup.subset_closure ⟨x,hx,rfl⟩
  change W = ⊤
  apply spanning_of_full_cosets (elementClosure a) D (runReference a D data) W
  · simpa only [runReference_quotient] using hquot
  · intro i k
    apply full_elementClosure_fibre_mem a (runReference a D data i) D W _ k
    intro b hb j hj
    have hjl : j < (data[i.val]).1 := lt_of_lt_of_le hj (hD i)
    exact actual_fixed_fibre_mem a D data hne hC hr hl Q R L hV hA W hW i j hjl
      (hlayer (retainedLayerEquiv a D data hne ⟨i,⟨j,by omega⟩⟩)) ⟨b,hb⟩

end DirectedCycles
