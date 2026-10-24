import DirectedCycles.LocalPowerSegmentRestriction
import DirectedCycles.LocalGlobalWordPowers

set_option autoImplicit false
namespace DirectedCycles.LocalGroupAlgebra
variable {G : Type*} [Group G] (W : Set G) (h1 : (1 : G) ∈ W)
    (hi : ∀ x ∈ W, x⁻¹ ∈ W)

/-- Actual ambient powers staying in a finite window give every local
bracketing, not merely a left-associated product. -/
theorem restricted_powerIn_of_powers (x : W) (B : Set W) (n : ℕ)
    (hp : ∀ j ≤ n, x.val^j ∈ Subtype.val '' B) :
    ((ofGroup G).restrict W h1 hi).PowerIn B x n := by
  classical
  let p : (ofGroup G).PowerSegment x.val n :=
    PowerSegment.of_add (ofGroup G) (fun j => x.val^j) (pow_zero _) (fun _ => pow_one _)
      (fun j k _ => (pow_add _ j k).symm)
  have hpW : ∀ j ≤ n, p.power j ∈ W := by
    intro j hj
    obtain ⟨y,_hy,he⟩ := hp j hj
    change x.val^j ∈ W
    exact he ▸ y.property
  let pr := p.restrict W h1 hi x.property hpW
  refine ⟨pr.power n,?_,pr.product n le_rfl⟩
  obtain ⟨y,hy,he⟩ := hp n le_rfl
  have he' : pr.power n = y := by
    apply Subtype.ext
    exact (p.restrict_value W h1 hi x.property hpW le_rfl).trans he.symm
  exact he'.symm ▸ hy
end DirectedCycles.LocalGroupAlgebra
