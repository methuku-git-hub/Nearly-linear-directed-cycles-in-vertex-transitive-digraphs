import DirectedCycles.NormGrowthNSS
import DirectedCycles.SubgroupNSSBasics
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false
namespace DirectedCycles
variable {A : Type*} [NormedRing A] [NormedSpace ℝ A]

/-- Squaring expands distance from the identity in a small normed-ring
ball. The quadratic error is bounded by submultiplicativity of the norm. -/
theorem normed_ring_doubling_growth (x : A) (hx : ‖x-1‖ ≤ 1/2) :
    (3/2)*‖x-1‖ ≤ ‖x*x-1‖ := by
  let a := x-1
  have he : a+a = (x*x-1)-a*a := by dsimp [a]; noncomm_ring
  have hn : ‖a+a‖ = 2*‖a‖ := by
    rw [← two_smul ℝ a,norm_smul]
    norm_num
  have hle := norm_sub_le (x*x-1) (a*a)
  rw [← he,hn] at hle
  have hmul := norm_mul_le a a
  have ha0 := norm_nonneg a
  change ‖a‖ ≤ 1/2 at hx
  change (3/2)*‖a‖ ≤ ‖x*x-1‖
  nlinarith

/-- The unit group of a real normed ring is NSS. Finite-dimensional
matrix representations can therefore supply NSS quotients without using
the closed-subgroup theorem for Lie groups. -/
theorem normed_ring_units_nss : HasNoSmallSubgroups Aˣ := by
  let V : Set Aˣ := {x | ‖(x : A)-1‖ < 1/2}
  have hVo : IsOpen V := isOpen_lt (Units.continuous_val.sub continuous_const).norm continuous_const
  have hV1 : (1 : Aˣ) ∈ V := by change ‖(1 : A)-1‖ < 1/2; norm_num
  have hcyclic : ∀ x : Aˣ, (∀ n : ℕ, x^n ∈ V) → x = 1 :=
    cyclic_nss_of_doubling_growth V (fun x => ‖(x : A)-1‖) (3/2) (1/2)
      (by norm_num) (fun _ _ => norm_nonneg _) (by
        intro x _ hx
        apply Units.ext
        exact sub_eq_zero.mp (norm_eq_zero.mp hx))
      (fun _ hx => hx.le) (by
        intro x hx _
        exact normed_ring_doubling_growth (x : A) hx.le)
  exact ⟨V,hVo,hV1,subgroup_free_of_cyclic_nss hcyclic⟩
end DirectedCycles
