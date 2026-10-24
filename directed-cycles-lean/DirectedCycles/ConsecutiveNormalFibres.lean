import DirectedCycles.TranslatedConsecutivePowers
import DirectedCycles.BaselineClosureCongruence
import DirectedCycles.BaselineQuotientPrefixes

set_option autoImplicit false
namespace DirectedCycles

/-- D consecutive complete B-fibres span each full K-fibre, where B=[G,a]
and K is the normal closure of a. This is the first fibre step in Lemma 5.7. -/
theorem full_elementClosure_fibre_mem {G : Type*} [Group G]
    (a g : G) (D : ℕ) (W : AddSubgroup (TruncatedGroupRing G D))
    (h : ∀ b ∈ elementCommutators a, ∀ j : ℕ, j < D →
      truncatedElement G D (b*g*a^j) ∈ W) :
    ∀ k : elementClosure a, truncatedElement G D (k.val*g) ∈ W := by
  intro k
  let q := QuotientGroup.mk' (elementCommutators a)
  obtain ⟨t,ht⟩ := elementClosure_quotient_power a k.val k.property
  have hc : Commute (q a) (q g) :=
    (Subgroup.mem_center_iff.mp (element_mod_commutators_central a) (q g)).symm
  have hq : q (k.val*g) = q (g*a^t) := by
    rw [map_mul,ht,map_mul,map_zpow]
    exact (hc.zpow_left t).eq
  obtain ⟨b,hb,hbkg⟩ := quotient_prefix_left_factor (elementCommutators a) (k.val*g) (g*a^t) hq
  have hm := translated_consecutive_powers_mem D a (b*g) W (h b hb) t
  rw [hbkg]
  simpa only [mul_assoc] using hm

end DirectedCycles
