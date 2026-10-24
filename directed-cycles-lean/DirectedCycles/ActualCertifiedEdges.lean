import DirectedCycles.ActualEdgeExpansion
import DirectedCycles.TemplateCertifiedEdges

set_option autoImplicit false
namespace DirectedCycles

/-- The actual expanded cycle records the connector and cyclic coordinate
of every non-a edge. These are the data used in return-walk separation. -/
theorem cyclic_auxiliary_cycle_expands_with_edge_data {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hC : cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a)
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hgap : ∀ i : Fin data.length, (data[i.val]).1+2*D+2 ≤
      orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (S : Set G) (ha : a ∈ S) (hs : ∀ i : Fin data.length, (data[i.val]).2 ∈ S)
    (Q : Cycle (cyclicAuxiliaryGraph a D data hne)) :
    ∃ C : Cycle (CayleyDigraph S), Q.length ≤ C.length ∧ C.ClosedUnderGenerator a ∧
      ∀ i, C.vertex (finRotate C.length i) = C.vertex i*a ∨
        ∃ p : Fin data.length, ∃ u : ℕ, u ≤ D ∧
          C.vertex (finRotate C.length i) = C.vertex i*(data[p.val]).2 ∧
          QuotientGroup.mk' (elementCommutators a) (C.vertex i) =
            QuotientGroup.mk' (elementCommutators a) (runReference a D data p)*
              (QuotientGroup.mk' (elementCommutators a) a)^((data[p.val]).1+u) := by
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
  obtain ⟨C,hL,hclosed,hR⟩ := E.simple_cycle_with_edge_data q (orderOf (q a)) hgap
    (pow_orderOf_eq_one (q a)) r hcoord hx S ha hlabel E.allowedStep E.allowedStep_word_chains
  refine ⟨C,hL,hclosed,?_⟩
  intro i
  rcases hR i with he | ⟨e,he,hxi,hyi⟩
  · exact Or.inl he
  · refine Or.inr ⟨E.position e,(E.choice e).val,by have := (E.choice e).isLt; omega,?_,?_⟩
    · exact hyi
    · change q (C.vertex i) = r (E.position e)*(q a)^(_+(E.choice e).val)
      rw [hxi,map_mul,map_pow,hx,he,pow_add,mul_assoc]

end DirectedCycles
