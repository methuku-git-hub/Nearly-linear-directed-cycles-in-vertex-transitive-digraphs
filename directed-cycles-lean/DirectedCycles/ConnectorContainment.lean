module

public import DirectedCycles.ConnectorAlgebra
public import DirectedCycles.OrbitDifferenceSpan

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- Actual connector labels in C supply the consecutive differences required
by the unipotent recurrence. The prefix is only required to lie in K g. -/
theorem connector_labels_consecutive {G : Type*} [Group G] (a g s p r : G)
    (D : ℕ) (C : Subgroup (elementCommutators a))
    (mu : Fin (D+1) → elementCommutators a)
    (hmu : ∀ j, (mu j).val = p*connectorWord a s D j.val*r⁻¹)
    (hC : ∀ j, mu j ∈ C)
    (hp : ∃ k ∈ elementClosure a, p = k*g) :
    ∃ m : ℤ, ∀ j : ℕ, j < D →
      (representationEquiv (normalAbelianAction (elementCommutators a)) a ^ (m+j))
        (elementCocycle a g-elementCocycle a (g*s)) ∈
          (C.map Abelianization.of).toAddSubgroup := by
  obtain ⟨k,hk,rfl⟩ := hp
  obtain ⟨m,hm⟩ := elementClosure_action_power a k hk
  let B := elementCommutators a
  let T := normalAbelianAction B
  let L := representationEquiv T a
  let b : B := ⟨⁅a,s⁆,by
    have h := B.inv_mem (mem_elementCommutators a s)
    simpa only [commutatorElement_inv] using h⟩
  refine ⟨m,?_⟩
  intro j hj
  let j₀ : Fin (D+1) := ⟨j,by omega⟩
  let j₁ : Fin (D+1) := ⟨j+1,by omega⟩
  have he : mu j₁*(mu j₀)⁻¹ = normalConjugation B (k*g) (normalConjugation B (a^j) b) := by
    apply Subtype.ext
    change (mu j₁).val*((mu j₀).val)⁻¹ = (k*g)*(a^j*⁅a,s⁆*(a^j)⁻¹)*(k*g)⁻¹
    rw [hmu j₁,hmu j₀]
    have hword := connectorWord_difference a s D j hj
    change _ = _ at hword
    change (k*g)*connectorWord a s D (j+1)*r⁻¹*
      ((k*g)*connectorWord a s D j*r⁻¹)⁻¹ = _
    rw [← hword]
    group
  have hmem : normalAbelianElement B (mu j₁*(mu j₀)⁻¹) ∈
      (C.map Abelianization.of).toAddSubgroup := by
    exact Subgroup.mem_map_of_mem Abelianization.of (C.mul_mem (hC j₁) (C.inv_mem (hC j₀)))
  rw [he,← normalAbelianAction_element,← normalAbelianAction_element] at hmem
  change T (k*g) (T (a^j) (normalAbelianElement B b)) ∈ _ at hmem
  rw [map_mul,Module.End.mul_apply,hm] at hmem
  have hc : T g (T (a^j) (normalAbelianElement B b)) =
      T (a^j) (T g (normalAbelianElement B b)) := by
    have h := (elementCocycle_action_commute a g).pow_right j
    rw [← map_pow] at h
    exact congrArg (fun f : Module.End ℤ (NormalAbelianModule B) => f (normalAbelianElement B b)) h.eq
  rw [hc,elementCocycle_adjacent_difference] at hmem
  rw [← zpow_natCast a j,representationEquiv_zpow,← LinearEquiv.mul_apply,← zpow_add] at hmem
  exact hmem

end DirectedCycles
