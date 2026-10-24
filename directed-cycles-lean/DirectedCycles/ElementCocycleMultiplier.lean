import DirectedCycles.ElementPolynomialCocycle
import DirectedCycles.NilpotentMultiplier
import DirectedCycles.NilpotentSubgroupIndex

set_option autoImplicit false
namespace DirectedCycles

/-- The actual polynomial cocycle transfers the augmentation multiplier into
an invariant submodule of B/B'. The containment assumptions are later supplied
by the connector labels. -/
theorem elementCocycle_multiplier {G : Type*} [Group G] [Group.IsNilpotent G]
    (a : G) (n : ℕ) (hn : Group.nilpotencyClass G ≤ n) (m : ℕ)
    (E : Set (G ⧸ elementClosure a))
    (W : Submodule ℤ (NormalAbelianModule (elementCommutators a)))
    (hW : W ≤ W.comap (normalAbelianAction (elementCommutators a) a))
    (hE : ∀ g ∈ E, elementFactorCocycle a g ∈ W.map (elementDifferenceRange a).mkQ)
    (hm : ∀ z : TruncatedGroupRing (G ⧸ elementClosure a) (n+1),
      m • z ∈ AddSubgroup.closure (truncatedElement (G ⧸ elementClosure a) (n+1) '' E)) :
    ∀ v : NormalAbelianModule (elementCommutators a), m^(n+1) • v ∈ W := by
  let N := 1-normalAbelianAction (elementCommutators a) a
  have hNW : W ≤ W.comap N := fun v hv => W.sub_mem hv (hW hv)
  have hnil : N^(n+1) = 0 := by
    have h := normalAbelianAction_unipotent (elementCommutators a) (n+1)
      (hn.trans (Nat.le_succ n)) a
    change (1-normalAbelianAction (elementCommutators a) a)^(n+1) = 0
    rw [show (1-normalAbelianAction (elementCommutators a) a) =
      -(normalAbelianAction (elementCommutators a) a-1) by abel,neg_pow,h,mul_zero]
  apply multiplier_mem_of_nilpotent_range N W m (n+1) hNW hnil
  apply multiplier_mem_sup_range N W m
  intro v
  let F := elementPolynomialCocycle a n hn
  obtain ⟨z,hz⟩ := elementPolynomialCocycle_surjective a n hn ((elementDifferenceRange a).mkQ v)
  have hclosure : AddSubgroup.closure (truncatedElement (G ⧸ elementClosure a) (n+1) '' E) ≤
      (W.map (elementDifferenceRange a).mkQ).toAddSubgroup.comap F := by
    apply ((W.map (elementDifferenceRange a).mkQ).toAddSubgroup.comap F).closure_le.mpr
    rintro x ⟨g,hg,rfl⟩
    change elementPolynomialCocycle a n hn (truncatedElement (G ⧸ elementClosure a) (n+1) g) ∈
      W.map (elementDifferenceRange a).mkQ
    rw [elementPolynomialCocycle,truncatedCocycleMap_element]
    exact hE g hg
  have h := hclosure (hm z)
  change F (m • z) ∈ W.map (elementDifferenceRange a).mkQ at h
  rw [map_nsmul,hz] at h
  exact h

/-- The index consequence with the exact weighted central-series exponent.
The remaining geometric obligation is to supply W and its containments from
an actual cyclic connector construction. -/
theorem elementCocycle_subgroup_index {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (a : G) (r c n : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hn : c ≤ n) (m : ℕ) (hmpos : 0 < m) (E : Set (G ⧸ elementClosure a))
    (C : Subgroup (elementCommutators a))
    (W : Submodule ℤ (NormalAbelianModule (elementCommutators a)))
    (hW : W ≤ W.comap (normalAbelianAction (elementCommutators a) a))
    (hCW : W.toAddSubgroup ≤ (C.map Abelianization.of).toAddSubgroup)
    (hE : ∀ g ∈ E, elementFactorCocycle a g ∈ W.map (elementDifferenceRange a).mkQ)
    (hm : ∀ z : TruncatedGroupRing (G ⧸ elementClosure a) (n+1),
      m • z ∈ AddSubgroup.closure (truncatedElement (G ⧸ elementClosure a) (n+1) '' E)) :
    C.index ≤ m^((n+1)*∑ i ∈ Finset.range (c/2),
      (i+1)*(∑ j ∈ Finset.range c, r^(j+1))^(i+1)) := by
  have hv := elementCocycle_multiplier a n (hc.trans hn) m E W hW hE hm
  have hpow : ∀ x : Abelianization (elementCommutators a),
      x^(m^(n+1)) ∈ C.map Abelianization.of := by
    intro x
    exact hCW (hv (Additive.ofMul x))
  have hi := nilpotent_subgroup_index_of_abelian_power C (m^(n+1)) (pow_pos hmpos _) hpow
    (∑ j ∈ Finset.range c, r^(j+1)) (c/2)
    (nilpotent_subgroup_rank_bound r c hr hc (elementCommutators a))
    (commutator_subgroup_class_le_half (elementCommutators a) (elementCommutators_le_derived a) c hc)
  simpa only [pow_mul] using hi

end DirectedCycles
