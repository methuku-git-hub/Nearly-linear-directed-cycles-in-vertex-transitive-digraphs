import DirectedCycles.CentralPowerCoverage
import DirectedCycles.LowerCentralFactors

set_option autoImplicit false
open scoped commutatorElement
universe u
namespace DirectedCycles

/-- Power coverage modulo the derived group survives a surjective homomorphism. -/
theorem abelian_power_coverage_map {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (C : Subgroup G) (m : ℕ)
    (h : ∀ x : G, x^m ∈ C ⊔ commutator G) :
    ∀ y : Q, y^m ∈ C.map f ⊔ commutator Q := by
  intro y
  obtain ⟨x,rfl⟩ := hf y
  have hx := Subgroup.mem_map_of_mem f (h x)
  rw [map_pow,Subgroup.map_sup] at hx
  simpa only [commutator,Subgroup.map_commutator,Subgroup.map_top_of_surjective f hf] using hx

/-- Power coverage propagates down the lower central series with weight j
contributing the exponent m^j. No normality of C is assumed. -/
theorem lowerSeries_power_coverage (i m : ℕ) :
    ∀ {G : Type u} [Group G] (C : Subgroup G),
    (∀ x : G, x^m ∈ C ⊔ commutator G) →
    ∀ x ∈ lowerSeries G i, x^(m^(i+1)) ∈ C ⊔ lowerSeries G (i+1) := by
  induction i with
  | zero =>
    intro G _ C h x _
    simpa only [Nat.zero_add,pow_one,lowerSeries,Subgroup.top_lowerCentralSeries_one] using h x
  | succ i ih =>
    intro G _ C h x hx
    let Q := G ⧸ lowerSeries G (i+1+1)
    let f := QuotientGroup.mk' (lowerSeries G (i+1+1))
    have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
    let CQ := C.map f
    let H := lowerSeries Q i
    let K := lowerSeries Q (i+1)
    have hcentral : ⁅H,(⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q :=
      lowerSeries_central_mod_next G (i+1)
    have hKH : K ≤ H := Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ i)
    have hbase : ∀ y : Q, y^m ∈ CQ ⊔ commutator Q := abelian_power_coverage_map f hf C m h
    have ha : ∀ y : H, ∃ c : H, c.val ∈ CQ ∧ ∃ z : Subgroup.center Q,
        y.val^(m^(i+1)) = c.val*z.val := by
      intro y
      have hy := ih CQ hbase y.val y.property
      obtain ⟨c,hc,z,hz,he⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      have hcH : c ∈ H := by
        have hh := H.mul_mem (H.pow_mem y.property (m^(i+1))) (H.inv_mem (hKH hz))
        rw [← he,mul_inv_cancel_right] at hh
        exact hh
      exact ⟨⟨c,hcH⟩,hc,⟨z,hcentral hz⟩,he.symm⟩
    have hb : ∀ y : Q, ∃ d ∈ CQ, ∃ w ∈ commutator Q, y^m = d*w := by
      intro y
      obtain ⟨d,hd,w,hw,he⟩ := Subgroup.mem_sup_of_normal_right.mp (hbase y)
      exact ⟨d,hd,w,hw,he.symm⟩
    have hxQ : f x ∈ K := by
      change f x ∈ lowerSeries Q (i+1)
      rw [← lowerSeries_map f hf (i+1)]
      exact Subgroup.mem_map_of_mem f hx
    have hp := central_commutator_subgroup_power_mem H CQ hcentral (m^(i+1)) m ha hb (f x) hxQ
    have hmem : x^(m^(i+1+1)) ∈ (C.map f).comap f := by
      change f (x^(m^(i+1+1))) ∈ CQ
      rw [map_pow,pow_succ]
      exact hp
    rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk'] at hmem
    exact hmem

end DirectedCycles
