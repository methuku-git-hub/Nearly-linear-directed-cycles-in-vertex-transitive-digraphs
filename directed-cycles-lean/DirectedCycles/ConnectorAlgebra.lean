import DirectedCycles.ElementCocycle
import DirectedCycles.RepresentationEquiv

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- The words used to move the distinguished label through a connector. -/
def connectorWord {G : Type*} [Group G] (a s : G) (D j : ℕ) : G :=
  a^j*s*a^(D-j)

/-- Consecutive connector words differ by a conjugate commutator. -/
theorem connectorWord_difference {G : Type*} [Group G] (a s : G) (D j : ℕ) (hj : j < D) :
    connectorWord a s D (j+1) * (connectorWord a s D j)⁻¹ = a^j*⁅a,s⁆*(a^j)⁻¹ := by
  have hd : D-j = D-(j+1)+1 := by omega
  simp only [connectorWord,hd,pow_succ,commutatorElement_def]
  group

/-- Multiplication of prefixes gives the adjacent commutator-cocycle difference. -/
theorem elementCocycle_adjacent_difference {G : Type*} [Group G] (a g s : G) :
    normalAbelianAction (elementCommutators a) g
      (normalAbelianElement _ ⟨⁅a,s⁆,by
        have h := (elementCommutators a).inv_mem (mem_elementCommutators a s)
        simpa only [commutatorElement_inv] using h⟩) =
      elementCocycle a g-elementCocycle a (g*s) := by
  have he : (⟨⁅a,s⁆,by
      have h := (elementCommutators a).inv_mem (mem_elementCommutators a s)
      simpa only [commutatorElement_inv] using h⟩ : elementCommutators a) =
      (⟨⁅s,a⁆,mem_elementCommutators a s⟩ : elementCommutators a)⁻¹ :=
    Subtype.ext (commutatorElement_inv _ _).symm
  rw [he,normalAbelianElement_inv,map_neg,elementCocycle_identity a g s]
  change -normalAbelianAction _ g (elementCocycle a s) = _
  abel

/-- Every element of K acts by an integer power of L on B/B'. -/
theorem elementClosure_action_power {G : Type*} [Group G] (a k : G) (hk : k ∈ elementClosure a) :
    ∃ m : ℤ, ∀ v : NormalAbelianModule (elementCommutators a),
      normalAbelianAction (elementCommutators a) k v =
        (representationEquiv (normalAbelianAction (elementCommutators a)) a ^ m) v := by
  obtain ⟨z,hz,b,hb,he⟩ := Subgroup.mem_sup_of_normal_right.mp hk
  obtain ⟨m,rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨m,?_⟩
  intro v
  rw [← he,map_mul,normalAbelianAction_internal (elementCommutators a) ⟨b,hb⟩,mul_one]
  exact representationEquiv_zpow _ a m v

end DirectedCycles
