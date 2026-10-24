import DirectedCycles.SeparatedRunChoice
import DirectedCycles.CollisionConstraintDegree
import DirectedCycles.RunSeparation

set_option autoImplicit false
namespace DirectedCycles

/-- Actual choices of normalized residues and run lengths for all
right-multiplication collision constraints at once. -/
theorem choose_collision_separated_runs {I K H : Type*} [Group H]
    [Fintype I] [Fintype K] [DecidableEq I]
    (h q D : ℕ) [NeZero h] (hh : 8*(q+1)*(D+1) < h)
    (hK : Fintype.card K ≤ q) (σ : Equiv.Perm I) (hσ : ∀ i, σ i ≠ i)
    (start finish : I ↪ H) (label : K → H)
    (e : RightCollision start finish label → ZMod h) (ν : I → ZMod h) (i₀ : I) :
    ∃ v : I → ZMod h, ∃ l : I → ℕ,
      v (σ i₀)+(D : ZMod h)+ν i₀ = 0 ∧
      (∀ i, l i = (v i-v (σ i)-((D : ZMod h)+ν i)).val) ∧
      (∀ i, D ≤ l i ∧ (h+7)/8 ≤ l i ∧ l i ≤ h-2*D-2) ∧
      ((∑ i, ((l i : ZMod h)+(D : ZMod h)))+∑ i,ν i = 0) ∧
      (Fintype.card I*h ≤ 8*∑ i,(l i+1)) ∧
      (∀ c : RightCollision start finish label,
        v c.val.2.2-v c.val.2.1 ∉ collisionForbiddenResidues h D (e c)) := by
  classical
  let C := RightCollision start finish label
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨v,hv,hc⟩ := choose_separated_run_residues h q D hh σ hσ ν
    (fun c : C => c.val.2.1) (fun c : C => c.val.2.2)
    (fun c => collisionForbiddenResidues h D (e c)) (fun c => c.property.2)
    (fun c => collisionForbiddenResidues_card h D (e c)) (fun i =>
      (right_collision_degree start finish label i).trans (Nat.mul_le_mul_left 2 hK))
  obtain ⟨w,hw,hdiff⟩ := normalize_run_residues σ v ν (D : ZMod h) i₀
  let l := fun i => (w i-w (σ i)-((D : ZMod h)+ν i)).val
  have hbounds : ∀ i, D ≤ l i ∧ (h+7)/8 ≤ l i ∧ l i ≤ h-2*D-2 := by
    intro i
    have hi := hv i
    dsimp only [l]
    rw [hdiff]
    exact ⟨(separated_run_lower h q D hh).1.trans hi.1,hi⟩
  refine ⟨w,l,hw,fun _ => rfl,hbounds,residue_run_closure h D σ w ν,?_,?_⟩
  · have hceil : h ≤ 8*((h+7)/8) := by omega
    calc Fintype.card I*h = ∑ _i : I,h := by simp
      _ ≤ ∑ i,8*(l i+1) := Finset.sum_le_sum (fun i _ => by have := (hbounds i).2.1; omega)
      _ = 8*∑ i,(l i+1) := (Finset.mul_sum ..).symm
  · intro c
    rw [hdiff]
    exact hc c

end DirectedCycles
