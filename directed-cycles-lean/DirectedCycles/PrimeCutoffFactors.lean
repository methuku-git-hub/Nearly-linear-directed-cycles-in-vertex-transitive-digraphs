import DirectedCycles.SpanningAuxiliaryCycle

set_option autoImplicit false
namespace DirectedCycles

theorem AbovePrimeCutoff.elementClosure_factor_large {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] {D : ℕ} (hp : AbovePrimeCutoff G D) (a : G) (ha : a ≠ 1) :
    8*D+4 < Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a)) := by
  let h := Nat.card (elementClosure a ⧸ (elementCommutators a).subgroupOf (elementClosure a))
  have htwo : 2 ≤ h := elementClosure_factor_card_ge_two a ha
  have hprime := Nat.minFac_prime (show h ≠ 1 by omega)
  have hdvd : h ∣ Nat.card G :=
    ((elementCommutators a).subgroupOf (elementClosure a)).card_quotient_dvd_card.trans
      (elementClosure a).card_subgroup_dvd_card
  exact (hp _ hprime ((Nat.minFac_dvd h).trans hdvd)).trans_le (Nat.minFac_le (by omega))

theorem elementClosure_one {G : Type*} [Group G] : elementClosure (1 : G) = ⊥ := by
  rw [elementClosure_eq_normalClosure]
  apply le_bot_iff.mp
  apply Subgroup.normalClosure_le_normal
  intro x hx
  change x = 1
  exact hx

theorem nonidentity_of_prime_dvd_elementClosure {G : Type*} [Group G]
    (a : G) (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card (elementClosure a)) : a ≠ 1 := by
  intro he
  rw [he,elementClosure_one] at hd
  have hcard : Nat.card (⊥ : Subgroup G) = 1 := Nat.card_eq_one_iff_unique.mpr
    ⟨inferInstance,inferInstance⟩
  rw [hcard] at hd
  exact hp.not_dvd_one hd

end DirectedCycles
