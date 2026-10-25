module

public import DirectedCycles.ConnectorContainment
public import DirectedCycles.ElementCocycleMultiplier

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- The algebraic index estimate for a concrete system of cyclic connector
words. All containment assumptions refer to the explicitly displayed labels;
no polynomial-map, nilpotence, or index premise is left to assume. -/
theorem connector_system_index_of_multiplier {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (a : G) (r c n ell : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hn : c ≤ n) (C : Subgroup (elementCommutators a))
    (g : Fin (ell+1) → G) (s p t : Fin ell → G) (h0 : g 0 = 1)
    (hstep : ∀ i : Fin ell, g i.succ = g i.castSucc*s i)
    (hp : ∀ i, ∃ k ∈ elementClosure a, p i = k*g i.castSucc)
    (mu : Fin ell → Fin (n+1+1) → elementCommutators a)
    (hmu : ∀ i j, (mu i j).val = p i*connectorWord a (s i) (n+1) j.val*(t i)⁻¹)
    (hC : ∀ i j, mu i j ∈ C)
    (m : ℕ) (hmpos : 0 < m)
    (hm : ∀ z : TruncatedGroupRing (G ⧸ elementClosure a) (n+1), m • z ∈
      AddSubgroup.closure (truncatedElement (G ⧸ elementClosure a) (n+1) ''
        Set.range (fun i : Fin ell => QuotientGroup.mk' (elementClosure a) (g i.castSucc)))) :
    C.index ≤ m^((n+1)*∑ i ∈ Finset.range (c/2),
      (i+1)*(∑ j ∈ Finset.range c, r^(j+1))^(i+1)) := by
  classical
  let T := normalAbelianAction (elementCommutators a)
  let L := representationEquiv T a
  let v : Fin (ell+1) → NormalAbelianModule (elementCommutators a) := elementCocycle a ∘ g
  let W := orbitDifferenceSpan L v
  have hnil : (L.toLinearMap-1)^(n+1) = 0 :=
    normalAbelianAction_unipotent (elementCommutators a) (n+1)
      (hc.trans (hn.trans (Nat.le_succ n))) a
  have hcons : ∀ i : Fin ell, ∃ shift : ℤ, ∀ j : ℕ, j < n+1 →
      (L^(shift+j)) (v i.castSucc-v i.succ) ∈ (C.map Abelianization.of).toAddSubgroup := by
    intro i
    obtain ⟨shift,hshift⟩ := connector_labels_consecutive a (g i.castSucc) (s i) (p i) (t i)
      (n+1) C (mu i) (hmu i) (hC i) (hp i)
    refine ⟨shift,?_⟩
    intro j hj
    change (L^(shift+j)) (elementCocycle a (g i.castSucc)-elementCocycle a (g i.succ)) ∈ _
    rw [hstep i]
    exact hshift j hj
  choose shift hshift using hcons
  have hWC : W ≤ (C.map Abelianization.of).toAddSubgroup :=
    orbitDifferenceSpan_le L v _ (n+1) hnil shift hshift
  have hv0 : v 0 = 0 := by
    change elementCocycle a (g 0) = 0
    rw [h0]
    exact cocycle_one (elementCocycle_identity a)
  have hv : ∀ i, v i ∈ W := orbitDifferenceSpan_contains L v hv0
  have hstable : W.toIntSubmodule ≤ W.toIntSubmodule.comap (T a) := by
    intro x hx
    have h := orbitDifferenceSpan_stable L v 1 x hx
    change L x ∈ W
    simpa only [zpow_one] using h
  apply elementCocycle_subgroup_index a r c n hr hc hn m hmpos _ C W.toIntSubmodule hstable hWC _ hm
  rintro x ⟨i,rfl⟩
  exact ⟨v i.castSucc,hv i.castSucc,rfl⟩

/-- In the spanning case the concrete connector subgroup is all of B. -/
theorem connector_system_eq_top_of_spanning {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (a : G) (n ell : ℕ) (hn : Group.nilpotencyClass G ≤ n)
    (C : Subgroup (elementCommutators a))
    (g : Fin (ell+1) → G) (s p t : Fin ell → G) (h0 : g 0 = 1)
    (hstep : ∀ i : Fin ell, g i.succ = g i.castSucc*s i)
    (hp : ∀ i, ∃ k ∈ elementClosure a, p i = k*g i.castSucc)
    (mu : Fin ell → Fin (n+1+1) → elementCommutators a)
    (hmu : ∀ i j, (mu i j).val = p i*connectorWord a (s i) (n+1) j.val*(t i)⁻¹)
    (hC : ∀ i j, mu i j ∈ C)
    (hspan : AddSubgroup.closure (truncatedElement (G ⧸ elementClosure a) (n+1) ''
        Set.range (fun i : Fin ell => QuotientGroup.mk' (elementClosure a) (g i.castSucc))) = ⊤) :
    C = ⊤ := by
  have hi := connector_system_index_of_multiplier a (Group.rank G) n n ell le_rfl hn le_rfl
    C g s p t h0 hstep hp mu hmu hC 1 (by omega) (fun z => by rw [hspan]; trivial)
  simp only [one_pow] at hi
  apply C.index_eq_one.mp
  exact Nat.le_antisymm hi (Nat.pos_of_ne_zero C.index_ne_zero_of_finite)

end DirectedCycles
