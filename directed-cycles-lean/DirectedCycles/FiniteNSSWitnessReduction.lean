module

public import DirectedCycles.FiniteNSSProgressionRestoration
public import DirectedCycles.LocalZeroDimensionalProgression

@[expose] public section

set_option autoImplicit false
open scoped Pointwise BigOperators
namespace DirectedCycles

/-- The finite strong-group reduction can now consume the exact local
progression invariant in its genuine NSS quotient. Kernel restoration and
ambient inclusion preserve rank, step and density without new assumptions. -/
theorem strong_finite_nss_witness_reduction {G : Type*} [Group G] [Fintype G]
    {K : ℕ} {A : Finset G} (hA : IsStrongFiniteApproximateGroup K A) :
    ∃ H : Subgroup (Subgroup.closure (A : Set G)), ∃ hH : H.Normal,
      letI := hH
      let U := Subgroup.closure (A : Set G)
      let B := U.subtype ⁻¹' (A : Set G)
      let q := QuotientGroup.mk' H
      IsApproximateSubgroup (K : ℝ) (q '' B) ∧
      (∀ y : U ⧸ H, (∀ n : ℕ, y^n ∈ q '' B) → y = 1) ∧
      ∀ r c : ℕ, ∀ W : (LocalGroupAlgebra.ofGroup (U ⧸ H)).ProgressionWitness (q '' B) r c,
        ∀ J : ℕ, Nat.card (q '' B) ≤ J * ∏ j, (2*W.lengths j+1) →
        ∃ P : CosetNilprogression G r c,
          P.carrier ⊆ (A : Set G)^2 ∧ Nat.card (A : Set G) ≤ J*Nat.card P.carrier := by
  obtain ⟨H,hH,hq,hNSS,hrestore⟩ := strong_finite_nss_quotient_with_restoration hA
  let := hH
  refine ⟨H,hH,hq,hNSS,?_⟩
  intro r c W J hcard
  obtain ⟨Q,hQ,hQcard⟩ := global_progression_of_witness W _ J hcard
  exact hrestore r c Q hQ J hQcard
end DirectedCycles
