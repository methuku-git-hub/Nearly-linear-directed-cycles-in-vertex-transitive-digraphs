import DirectedCycles.ActualEdgeExpansion
import DirectedCycles.ActualTailSpanning

set_option autoImplicit false
namespace DirectedCycles

/-- Lemma 5.7 for the actual cyclic lift: a simple expanded cycle preserves
length and every occupied a-successor, and its a-edge tails span whenever the
quotient vertices and all auxiliary B-coordinate layers span. The group
containment, coordinate separation and word data are all proved internally. -/
theorem expanding_layer_cycle {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ []) (nu : ℤ)
    (hnu : QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod =
      (QuotientGroup.mk' (elementCommutators a) a)^nu)
    (hcong : (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) : ℤ) ∣
      ((data.map (fun z => z.1+D)).sum : ℤ)+nu)
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hbound : ∀ i : Fin data.length, D ≤ (data[i.val]).1 ∧ (data[i.val]).1+2*D+2 ≤
      Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)))
    (S : Set G) (ha : a ∈ S) (hs : ∀ i : Fin data.length, (data[i.val]).2 ∈ S)
    (Q : Cycle (cyclicAuxiliaryGraph a D data hne)) :
    ∃ C : Cycle (CayleyDigraph S), Q.length ≤ C.length ∧ C.ClosedUnderGenerator a ∧
      (SpansTruncation D (Set.range (fun i : Fin data.length =>
        QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc))) →
       (∀ z, SpansTruncation D (auxiliaryLayerCoordinates a D data hne Q z)) →
       SpansTruncation D (C.generatorTails a)) := by
  have hC := cyclicAuxiliaryGroup_le_of_congruence a D data hne nu hnu hcong
  have hgap : ∀ i : Fin data.length, (data[i.val]).1+2*D+2 ≤
      orderOf (QuotientGroup.mk' (elementCommutators a) a) := by
    intro i
    simpa only [elementClosure_factor_card_eq_orderOf] using (hbound i).2
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
  obtain ⟨C,_,hL,hV,hA⟩ := E.simple_cycle_with_edge_condition q (orderOf (q a)) hgap (pow_orderOf_eq_one (q a))
    r hcoord hx S ha hlabel
  refine ⟨C,hL,hA,?_⟩
  intro hquot hlayer
  exact actual_expanded_tails_span a D data hne hC hr hl (fun i => (hbound i).1)
    Q hquot hlayer (CayleyDigraph S) C hV hA

end DirectedCycles
