import DirectedCycles.LocalApproximateRestriction
import DirectedCycles.LocalQuotientHom
import DirectedCycles.GlobalToLocalApproximate

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

/-- The actual local quotient of a local approximate group preserves its
covering constant once every required word is shown to stay in the window. -/
theorem local_approximate_window_quotient [DecidablePred (· ∈ W)]
    [DecidableEq (hP.WindowQuotient hW1 hWi hW6)] {K : ℕ} {A : Finset G}
    (hA : IsLocalFiniteApproximateGroup (LocalGroupAlgebra.ofGroup G) K A)
    (hAW : (A : Set G)^200 ⊆ W) :
    IsLocalFiniteApproximateGroup (hP.quotientAlgebra hW1 hWi hW6) K
      ((A.subtype (· ∈ W)).image (hP.windowMk hW1 hWi hW6)) := by
  have hdom : ∀ n ≤ 200, (LocalGroupAlgebra.ofGroup G).wordPower (A : Set G) n ⊆ W := by
    intro n hn
    rw [LocalGroupAlgebra.ofGroup_wordPower]
    exact (Set.pow_subset_pow_right hA.one_mem hn).trans hAW
  exact (hA.restrict W hW1 (fun _ hx => LocalNormalSet.window_inv_mem hWi hx) hdom).image
    (hP.quotientHom hW1 hWi hW6)

/-- For the library convention, the same actual quotient has the explicitly
proved factor-two symmetric-cover conversion. -/
theorem global_approximate_window_quotient [DecidablePred (· ∈ W)]
    [DecidableEq (hP.WindowQuotient hW1 hWi hW6)] {K : ℕ} {A : Finset G}
    (hK : 1 ≤ K) (hA : IsApproximateSubgroup (K : ℝ) (A : Set G))
    (hAW : (A : Set G)^200 ⊆ W) :
    IsLocalFiniteApproximateGroup (hP.quotientAlgebra hW1 hWi hW6) (2*K)
      ((A.subtype (· ∈ W)).image (hP.windowMk hW1 hWi hW6)) :=
  local_approximate_window_quotient hP hW1 hWi hW6 (global_to_local_approximate hK hA) hAW
end DirectedCycles
