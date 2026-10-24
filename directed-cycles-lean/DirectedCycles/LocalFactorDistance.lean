import DirectedCycles.LocalWordPowers
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- Actual left factors taking an element of A to x. The factor x is always
available when A contains the identity, even when other products are undefined. -/
noncomputable def factorFinset (A : Finset G) (x : G) : Finset G := by
  classical
  exact Finset.univ.filter (fun u => ∃ a ∈ A, L.mulRel u a x)

theorem mem_factorFinset (A : Finset G) (x u : G) :
    u ∈ L.factorFinset A x ↔ ∃ a ∈ A, L.mulRel u a x := by
  classical
  simp only [factorFinset,Finset.mem_filter,Finset.mem_univ,true_and]

theorem factorFinset_nonempty (A : Finset G) (hA : L.one ∈ A) (x : G) :
    (L.factorFinset A x).Nonempty :=
  ⟨x,(L.mem_factorFinset A x x).2 ⟨L.one,hA,L.mul_one x⟩⟩

noncomputable def factorDistance (d : G → ℝ) (A : Finset G) (hA : L.one ∈ A) (x : G) : ℝ :=
  (L.factorFinset A x).inf' (L.factorFinset_nonempty A hA x) d

theorem factorDistance_nonneg {d : G → ℝ} (hd : ∀ x, 0 ≤ d x)
    (A : Finset G) (hA : L.one ∈ A) (x : G) : 0 ≤ L.factorDistance d A hA x := by
  apply Finset.le_inf'
  exact fun a _ => hd a

theorem factorDistance_le {d : G → ℝ} {A : Finset G} (hA : L.one ∈ A)
    {x u a : G} (ha : a ∈ A) (hm : L.mulRel u a x) :
    L.factorDistance d A hA x ≤ d u :=
  Finset.inf'_le _ ((L.mem_factorFinset A x u).2 ⟨a,ha,hm⟩)

theorem factorDistance_eq_zero {d : G → ℝ} (hd : ∀ x, 0 ≤ d x) (hd1 : d L.one = 0)
    {A : Finset G} (hA : L.one ∈ A) {x : G} (hx : x ∈ A) :
    L.factorDistance d A hA x = 0 := by
  apply le_antisymm _ (L.factorDistance_nonneg hd A hA x)
  simpa only [hd1] using L.factorDistance_le (d := d) hA hx (L.one_mul x)

/-- Outside the actual square, every factor lies outside A, so positive
separation from A transfers to factor distance. -/
theorem factorDistance_lower_outside_square {d : G → ℝ} {A : Finset G}
    (hA : L.one ∈ A) {r : ℝ} (hsep : ∀ u, u ∉ A → r ≤ d u)
    {x : G} (hx : x ∉ L.setMul (A : Set G) (A : Set G)) :
    r ≤ L.factorDistance d A hA x := by
  apply Finset.le_inf'
  intro u hu
  obtain ⟨a,ha,hm⟩ := (L.mem_factorFinset A x u).1 hu
  apply hsep
  exact fun huA => hx ⟨u,huA,a,ha,hm⟩
theorem exists_factorDistance_eq (d : G → ℝ) (A : Finset G) (hA : L.one ∈ A) (x : G) :
    ∃ u a, a ∈ A ∧ L.mulRel u a x ∧ L.factorDistance d A hA x = d u := by
  classical
  obtain ⟨u,hu,hmin⟩ := (L.factorFinset A x).exists_min_image d (L.factorFinset_nonempty A hA x)
  obtain ⟨a,ha,hm⟩ := (L.mem_factorFinset A x u).1 hu
  refine ⟨u,a,ha,hm,le_antisymm (L.factorDistance_le hA ha hm) ?_⟩
  apply Finset.le_inf'
  exact hmin
end LocalGroupAlgebra
end DirectedCycles
