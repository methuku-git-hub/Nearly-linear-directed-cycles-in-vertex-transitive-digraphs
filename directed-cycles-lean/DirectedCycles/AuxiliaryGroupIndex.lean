import DirectedCycles.ActualConnectorData
import DirectedCycles.BaselineClosureCongruence
import DirectedCycles.ConnectorDensityIndex

set_option autoImplicit false
namespace DirectedCycles

/-- Manuscript Lemma 5.5, density conclusion, for the actual constructed
auxiliary group. The source quotient-cycle vertices are required to be distinct. -/
theorem auxiliary_group_density_index {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (a : G) (r c n : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hn : c ≤ n) (data : List (ℕ × G)) (hne : data ≠ []) (nu : ℤ)
    (hg : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hnu : QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod =
      (QuotientGroup.mk' (elementCommutators a) a)^nu)
    (hcong : (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) : ℤ) ∣
      ((data.map (fun z => z.1+(n+1))).sum : ℤ)+nu) :
    (((cyclicAuxiliaryGroup a (n+1) data hne).subgroupOf (elementCommutators a)).index : ℝ) ≤
      auxiliaryIndexConstant r c n *
      ((Nat.card (G ⧸ elementClosure a) : ℝ)/data.length)^auxiliaryIndexExponent r c n := by
  have hclose := baseline_closure_of_congruence a (n+1) data nu hnu hcong
  obtain ⟨p,t,mu,hp,hmu,hC⟩ := cyclicAuxiliary_connector_data a (n+1) data hne hclose
  exact connector_system_density_index a r c n data.length hr hc hn (List.length_pos_iff.mpr hne)
    _ (cycleLabelPrefixes data) (fun i => (data[i.val]).2) p t (cycleLabelPrefixes_zero data)
    (cycleLabelPrefixes_step data) hg hp mu hmu hC

/-- Manuscript Lemma 5.5, spanning conclusion, for the same actual auxiliary
group. The equality is with B itself, not merely its image in an abelian quotient. -/
theorem auxiliary_group_eq_elementCommutators_of_spanning {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] (a : G) (n : ℕ) (hn : Group.nilpotencyClass G ≤ n)
    (data : List (ℕ × G)) (hne : data ≠ []) (nu : ℤ)
    (hnu : QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod =
      (QuotientGroup.mk' (elementCommutators a) a)^nu)
    (hcong : (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) : ℤ) ∣
      ((data.map (fun z => z.1+(n+1))).sum : ℤ)+nu)
    (hspan : AddSubgroup.closure (truncatedElement (G ⧸ elementClosure a) (n+1) ''
      Set.range (fun i : Fin data.length =>
        QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc))) = ⊤) :
    cyclicAuxiliaryGroup a (n+1) data hne = elementCommutators a := by
  have hclose := baseline_closure_of_congruence a (n+1) data nu hnu hcong
  obtain ⟨p,t,mu,hp,hmu,hC⟩ := cyclicAuxiliary_connector_data a (n+1) data hne hclose
  have he := connector_system_eq_top_of_spanning a n data.length hn _ (cycleLabelPrefixes data)
    (fun i => (data[i.val]).2) p t (cycleLabelPrefixes_zero data) (cycleLabelPrefixes_step data)
    hp mu hmu hC hspan
  exact le_antisymm (cyclicAuxiliaryGroup_le a (n+1) data hne hclose)
    (Subgroup.subgroupOf_eq_top.mp he)

end DirectedCycles
