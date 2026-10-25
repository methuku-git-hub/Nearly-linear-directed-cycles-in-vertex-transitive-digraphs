module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero vector has an actual continuous linear coordinate functional. -/
theorem exists_continuous_dual_eq_one (v : E) (hv : v ≠ 0) :
    ∃ ℓ : E →L[ℝ] ℝ, ℓ v = 1 := by
  obtain ⟨g,_,hg⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.2 hv)
  refine ⟨‖v‖⁻¹ • g,?_⟩
  simp only [smul_apply,smul_eq_mul,hg]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)

/-- The coordinate along a nonzero vector and the kernel of its functional
form an explicit topological direct sum. -/
noncomputable def vectorComplementEquiv (v : E) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1) :
    (ℝ × ℓ.ker) ≃L[ℝ] E := by
  let A : (ℝ × ℓ.ker) →L[ℝ] E := (ContinuousLinearMap.toSpanSingleton ℝ v).coprod ℓ.ker.subtypeL
  let b : E → ℓ.ker := fun x => ⟨x-(ℓ x) • v,by simp [map_sub,map_smul,hℓ]⟩
  refine {
    toLinearEquiv := {
      toLinearMap := A.toLinearMap
      invFun := fun x => (ℓ x,b x)
      left_inv := ?_
      right_inv := ?_
    }
    continuous_toFun := A.continuous
    continuous_invFun := ?_
  }
  · intro p
    apply Prod.ext
    · change ℓ (p.1 • v+(p.2 : E)) = p.1
      simp only [map_add,map_smul,hℓ,smul_eq_mul,mul_one]
      have hz : ℓ (p.2 : E) = 0 := p.2.property
      rw [hz,add_zero]
    · apply Subtype.ext
      change p.1 • v+(p.2 : E)-ℓ (p.1 • v+(p.2 : E)) • v = (p.2 : E)
      have hz : ℓ (p.2 : E) = 0 := p.2.property
      rw [map_add,map_smul,hℓ,hz,smul_eq_mul,mul_one,add_zero]
      abel
  · intro x
    change ℓ x • v+(x-ℓ x • v) = x
    abel
  · exact ℓ.continuous.prodMk ((continuous_id.sub (ℓ.continuous.smul continuous_const)).subtype_mk _)

/-- Formula for the constructed complement coordinates. -/
theorem vectorComplementEquiv_apply (v : E) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1)
    (p : ℝ × ℓ.ker) : vectorComplementEquiv v ℓ hℓ p = p.1 • v+(p.2 : E) := rfl
end DirectedCycles
