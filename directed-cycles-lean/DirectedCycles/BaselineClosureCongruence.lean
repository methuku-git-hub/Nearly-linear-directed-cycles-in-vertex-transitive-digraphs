module

public import DirectedCycles.CyclicAuxiliaryGraph

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The source parameter |K/B| is exactly the order of a in G/B. -/
theorem elementClosure_factor_card_eq_orderOf {G : Type*} [Group G] [Finite G] (a : G) :
    Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) =
      orderOf (QuotientGroup.mk' (elementCommutators a) a) := by
  rw [Nat.card_congr (subgroupQuotientEquivMap (elementClosure a) (elementCommutators a)).toEquiv,
    elementClosure_image,Nat.card_zpowers]

/-- The endpoint in K has the required integer exponent modulo B. -/
theorem elementClosure_quotient_power {G : Type*} [Group G]
    (a t : G) (ht : t ∈ elementClosure a) :
    ∃ nu : ℤ, QuotientGroup.mk' (elementCommutators a) t =
      (QuotientGroup.mk' (elementCommutators a) a)^nu := by
  have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' (elementCommutators a)) ht
  rw [elementClosure_image] at h
  obtain ⟨nu,hnu⟩ := Subgroup.mem_zpowers_iff.mp h
  exact ⟨nu,hnu.symm⟩

/-- The manuscript's numerical run-length congruence gives the exact baseline
closure equation, using h=|K/B| rather than assuming an element-order equality. -/
theorem baseline_closure_of_congruence {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (nu : ℤ)
    (hnu : QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod =
      (QuotientGroup.mk' (elementCommutators a) a)^nu)
    (hcong : (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) : ℤ) ∣
      ((data.map (fun z => z.1+D)).sum : ℤ)+nu) :
    (QuotientGroup.mk' (elementCommutators a) a)^((data.map (fun z => z.1+D)).sum) *
      QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod = 1 := by
  rw [hnu,← zpow_natCast,← zpow_add]
  apply orderOf_dvd_iff_zpow_eq_one.mp
  rwa [← elementClosure_factor_card_eq_orderOf] 

/-- The constructed auxiliary group is in B under the source congruence. -/
theorem cyclicAuxiliaryGroup_le_of_congruence {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ []) (nu : ℤ)
    (hnu : QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod =
      (QuotientGroup.mk' (elementCommutators a) a)^nu)
    (hcong : (Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) : ℤ) ∣
      ((data.map (fun z => z.1+D)).sum : ℤ)+nu) :
    cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a :=
  cyclicAuxiliaryGroup_le a D data hne (baseline_closure_of_congruence a D data nu hnu hcong)

end DirectedCycles
