module

public import Mathlib.Combinatorics.Additive.ApproximateSubgroup
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Convert the library's arbitrary covering set into BGT's symmetric cover
inside A cubed, with at most a factor two in the covering parameter. -/
theorem symmetric_approximate_cover {A : Set G} {K : ℕ}
    (hA : IsApproximateSubgroup (K : ℝ) A) :
    ∃ X : Finset G, X.card ≤ 2*K ∧ (∀ x ∈ X, x⁻¹ ∈ X) ∧ (X : Set G) ⊆ A^3 ∧ A^2 ⊆ (X : Set G)*A := by
  classical
  obtain ⟨F,hF,hcover⟩ := hA.sq_covBySMul
  have hFcard : F.card ≤ K := by exact_mod_cast hF
  let F₀ := F.filter (fun x => x ∈ A^3)
  let X := F₀ ∪ F₀⁻¹
  have hF0 : F₀.card ≤ K := (Finset.card_filter_le _ _).trans hFcard
  have hiA : ∀ x ∈ A, x⁻¹ ∈ A := by
    intro x hx
    have hh : x⁻¹ ∈ A⁻¹ := Set.inv_mem_inv.mpr hx
    simpa only [hA.inv_eq_self] using hh
  have hiA3 : (A^3)⁻¹ = A^3 := by rw [← inv_pow,hA.inv_eq_self]
  refine ⟨X,?_,?_,?_,?_⟩
  · have hh : X.card ≤ F₀.card+F₀.card := by
      simpa only [X,Finset.card_inv] using Finset.card_union_le F₀ (F₀⁻¹)
    omega
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · apply Finset.mem_union.mpr
      right
      simpa only [Finset.mem_inv',inv_inv] using hx
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inv'.mp hx))
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).2
    · have hh : x⁻¹ ∈ A^3 := (Finset.mem_filter.mp (Finset.mem_inv'.mp hx)).2
      have hi : (x⁻¹)⁻¹ ∈ (A^3)⁻¹ := Set.inv_mem_inv.mpr hh
      simpa only [inv_inv,hiA3] using hi
  · intro z hz
    obtain ⟨x,hx,y,hy,hxy⟩ := hcover hz
    change x*y = z at hxy
    have hx3 : x ∈ A^3 := by
      rw [show (3 : ℕ) = 2+1 by rfl,pow_succ]
      refine ⟨z,hz,y⁻¹,hiA y hy,?_⟩
      change z*y⁻¹ = x
      rw [← hxy,mul_assoc,mul_inv_cancel,mul_one]
    exact ⟨x,Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx,hx3⟩)),y,hy,hxy⟩
end DirectedCycles
