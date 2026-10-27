module

public import DirectedCycles.AuxiliaryExpansionTemplate
public import DirectedCycles.TemplateCycle

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The actual retained realization has precisely its asserted quotient
position and its fixed-run level. -/
theorem cyclicAuxiliary_realization_projection {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hC : cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a)
    (v : cyclicAuxiliaryGroup a D data hne × ZMod (slotBaseline (cyclicLiftSlots a D data)).length) :
    let p := (retainedLayerEquiv a D data hne).symm v.2
    QuotientGroup.mk' (elementCommutators a)
      (normalizedRealization (slotBaseline (cyclicLiftSlots a D data)) (v.1.val,v.2)) =
      QuotientGroup.mk' (elementCommutators a) (runReference a D data p.1)*
        (QuotientGroup.mk' (elementCommutators a) a)^p.2.val := by
  let p := (retainedLayerEquiv a D data hne).symm v.2
  have hb : QuotientGroup.mk' (elementCommutators a) v.1.val = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hC v.1.property)
  have hz : retainedLayerEquiv a D data hne p = v.2 :=
    (retainedLayerEquiv a D data hne).apply_symm_apply v.2
  have hv : v.2.val = (retainedPositionEquiv a D data p).val := by
    rw [← hz,retainedLayerEquiv_val]
  have hpref : ((slotBaseline (cyclicLiftSlots a D data)).take v.2.val).prod =
      runReference a D data p.1*a^p.2.val := by
    rw [hv,cyclicLiftSlots_baseline]
    exact cyclicBaseline_prefix_retained a D data p.1 p.2
  change QuotientGroup.mk' (elementCommutators a)
    (v.1.val*((slotBaseline (cyclicLiftSlots a D data)).take v.2.val).prod) = _
  rw [map_mul,hb,one_mul,hpref,map_mul,map_pow]

/-- Simplicity and length preservation in Lemma 5.7 for the actual constructed
auxiliary graph, with every positional and word hypothesis discharged. -/
theorem cyclic_auxiliary_cycle_expands {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hC : cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a)
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hgap : ∀ i : Fin data.length, (data[i.val]).1+2*D+2 ≤
      orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (S : Set G) (ha : a ∈ S) (hs : ∀ i : Fin data.length, (data[i.val]).2 ∈ S)
    (Q : Cycle (cyclicAuxiliaryGraph a D data hne)) :
    ∃ C : Cycle (CayleyDigraph S), Q.length ≤ C.length := by
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
  obtain ⟨C,_,hL,_⟩ := E.simple_cycle q (orderOf (q a)) hgap (pow_orderOf_eq_one (q a))
    r hcoord hx S ha hlabel
  exact ⟨C,hL⟩

end DirectedCycles
