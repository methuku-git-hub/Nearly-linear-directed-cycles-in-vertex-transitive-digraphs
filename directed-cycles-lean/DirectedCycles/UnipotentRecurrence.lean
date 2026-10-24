import DirectedCycles.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Span.Basic

set_option autoImplicit false
namespace DirectedCycles

/-- A difference of adjacent integer iterates is the corresponding iterate
of the first difference. -/
theorem linearEquiv_zpow_difference {V : Type*} [AddCommGroup V] [Module ℤ V]
    (L : V ≃ₗ[ℤ] V) (v : V) (k : ℤ) :
    (L ^ k) (L v - v) = (L ^ (k+1)) v - (L ^ k) v := by
  rw [map_sub, zpow_add, zpow_one]
  rfl

/-- D consecutive iterates of a vector killed by (L-I)^D generate every
integer iterate additively. The argument uses finite differences in both
directions and does not assume a torsion-free ambient group. -/
theorem unipotent_orbit_mem {V : Type*} [AddCommGroup V] [Module ℤ V]
    (L : V ≃ₗ[ℤ] V) (W : AddSubgroup V) (D : ℕ) (v : V)
    (hnil : ((L.toLinearMap - 1)^D) v = 0)
    (hfirst : ∀ i : ℕ, i < D → (L ^ (i : ℤ)) v ∈ W) :
    ∀ k : ℤ, (L ^ k) v ∈ W := by
  induction D generalizing v with
  | zero =>
    have hv : v = 0 := by simpa using hnil
    subst v
    intro k
    simp
  | succ D ih =>
    let w := L v - v
    have hw : ((L.toLinearMap - 1)^D) w = 0 := by
      rw [pow_succ] at hnil
      exact hnil
    have hfirstw : ∀ i : ℕ, i < D → (L ^ (i : ℤ)) w ∈ W := by
      intro i hi
      dsimp only [w]
      rw [linearEquiv_zpow_difference]
      exact W.sub_mem (by simpa only [Nat.cast_add, Nat.cast_one] using hfirst (i+1) (by omega))
        (hfirst i (by omega))
    have hw_all := ih w hw hfirstw
    have hv : v ∈ W := by simpa using hfirst 0 (by omega)
    intro k
    induction k using Int.induction_on with
    | zero => simpa using hv
    | succ k hk =>
      have h := W.add_mem (hw_all (k : ℤ)) hk
      dsimp only [w] at h
      rw [linearEquiv_zpow_difference, sub_add_cancel] at h
      exact h
    | pred k hk =>
      have h := W.sub_mem hk (hw_all (-(k : ℤ)-1))
      dsimp only [w] at h
      rw [linearEquiv_zpow_difference] at h
      have he : -(k : ℤ)-1+1 = -(k : ℤ) := by omega
      rw [he, sub_sub_cancel] at h
      exact h

/-- The same conclusion from any block of D consecutive integer iterates. -/
theorem unipotent_consecutive_orbit_mem {V : Type*} [AddCommGroup V] [Module ℤ V]
    (L : V ≃ₗ[ℤ] V) (W : AddSubgroup V) (D : ℕ)
    (hnil : (L.toLinearMap - 1)^D = 0) (v : V) (m : ℤ)
    (hfirst : ∀ i : ℕ, i < D → (L ^ (m + i)) v ∈ W) :
    ∀ k : ℤ, (L ^ k) v ∈ W := by
  have h : ∀ k : ℤ, (L ^ k) ((L ^ m) v) ∈ W := by
    apply unipotent_orbit_mem L W D
    · rw [hnil]
      rfl
    · intro i hi
      rw [← LinearEquiv.mul_apply, ← zpow_add, add_comm]
      exact hfirst i hi
  intro k
  have hk := h (k-m)
  rw [← LinearEquiv.mul_apply, ← zpow_add, sub_add_cancel] at hk
  exact hk

end DirectedCycles
