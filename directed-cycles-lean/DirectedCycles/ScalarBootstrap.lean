import Mathlib.Tactic

set_option autoImplicit false
namespace DirectedCycles

/-- A closed infimum argument for the Gleason bootstrap. It avoids choosing an
iteration count and keeps the limiting constant exact. -/
theorem scalar_bootstrap_bound {α : Type*} (u v : α → ℝ) (hv : ∀ x, 0 ≤ v x)
    {B θ : ℝ} (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hstart : ∃ X : ℝ, 0 ≤ X ∧ ∀ x, u x ≤ X*v x)
    (hstep : ∀ X : ℝ, 0 ≤ X → (∀ x, u x ≤ X*v x) →
      ∀ x, u x ≤ (B+θ*X)*v x) :
    ∀ x, u x ≤ (B/(1-θ))*v x := by
  let S : Set ℝ := {X | 0 ≤ X ∧ ∀ x, u x ≤ X*v x}
  have hSne : S.Nonempty := hstart
  have hSb : BddBelow S := ⟨0, fun _ h => h.1⟩
  let s := sInf S
  have hs0 : 0 ≤ s := le_csInf hSne (fun _ h => h.1)
  have hbound : ∀ x, u x ≤ s*v x := by
    intro x
    by_cases hx : v x = 0
    · obtain ⟨X,_,hX⟩ := hstart
      simpa [hx] using hX x
    · have hx0 : 0 < v x := lt_of_le_of_ne (hv x) (Ne.symm hx)
      have hh : u x / v x ≤ s := by
        apply le_csInf hSne
        intro X hX
        exact (div_le_iff₀ hx0).2 (hX.2 x)
      exact (div_le_iff₀ hx0).1 hh
  have hstepmem : B+θ*s ∈ S :=
    ⟨add_nonneg hB (mul_nonneg hθ hs0), hstep s hs0 hbound⟩
  have hsle : s ≤ B+θ*s := csInf_le hSb hstepmem
  have hsfinal : s ≤ B/(1-θ) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-θ)).2
    nlinarith
  intro x
  exact (hbound x).trans (mul_le_mul_of_nonneg_right hsfinal (hv x))
end DirectedCycles
