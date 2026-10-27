module

public import DirectedCycles.ActualCycleExpansion
public import DirectedCycles.TemplateEdgeCondition

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Actual cycle expansion preserves the distinguished-generator edge condition. -/
theorem cyclic_auxiliary_cycle_expands_with_edge_condition {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hC : cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a)
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hgap : ∀ i : Fin data.length, (data[i.val]).1+2*D+2 ≤
      orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (S : Set G) (ha : a ∈ S) (hs : ∀ i : Fin data.length, (data[i.val]).2 ∈ S)
    (Q : Cycle (cyclicAuxiliaryGraph a D data hne)) :
    ∃ C : Cycle (CayleyDigraph S), Q.length ≤ C.length ∧ C.ClosedUnderGenerator a := by
  have hl : ∀ i : Fin data.length, (data[i.val]).1 <
      orderOf (QuotientGroup.mk' (elementCommutators a) a) := by intro i; have := hgap i; omega
  let E := cyclicAuxiliary_expansionTemplate a D data hne hC hr hl Q
  let q := QuotientGroup.mk' (elementCommutators a)
  let r := fun i => q (runReference a D data i)
  have href : Function.Injective (fun i => QuotientGroup.mk' (elementClosure a) (runReference a D data i)) := by
    intro i j he
    apply hr
    simpa only [runReference_quotient] using he
  have hcoord := element_power_coordinates_injective a (runReference a D data) href
  have hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e) := by
    intro e
    exact cyclicAuxiliary_realization_projection a D data hne hC (Q.vertex e)
  have hlabel : ∀ e, E.label e ∈ S := by
    intro e
    exact hs ((retainedLayerEquiv a D data hne).symm (Q.vertex e).2).1
  obtain ⟨C,_,hL,_,hA⟩ := E.simple_cycle_with_edge_condition q (orderOf (q a)) hgap (pow_orderOf_eq_one (q a))
    r hcoord hx S ha hlabel
  exact ⟨C,hL,hA⟩

end DirectedCycles
