import DirectedCycles.NilpotentRanks
import Mathlib.Algebra.Group.Subgroup.Finite

set_option autoImplicit false
namespace DirectedCycles

/-- A coarse uniform generator bound for a finite power of a group.
The exponential bound avoids making any minimal-generation assumption. -/
theorem finite_power_group_rank_bound {ι B : Type*} [Fintype ι] [Group B] [Finite B]
    (r : ℕ) (hr : Group.rank B ≤ r) : Group.rank (ι → B) ≤ (r+1)^Fintype.card ι := by
  classical
  obtain ⟨s,hs,hgen⟩ := Group.rank_spec B
  let T := Fintype.piFinset (fun _ : ι => insert (1 : B) s)
  have hTcoe : (T : Set (ι → B)) = Set.pi Set.univ (fun _ => insert (1 : B) (s : Set B)) := by
    ext f
    simp [T]
  have hgenT : Subgroup.closure (T : Set (ι → B)) = ⊤ := by
    rw [hTcoe,Subgroup.closure_pi (fun _ => Set.mem_insert 1 _)]
    have hsingle : Subgroup.closure (insert (1 : B) (s : Set B)) = ⊤ := by
      rw [Subgroup.closure_insert_one,hgen]
    simp only [hsingle,Subgroup.pi_top]
  have hcard : T.card = (insert (1 : B) s).card^Fintype.card ι := by
    simp [T]
  have hc : (insert (1 : B) s).card ≤ r+1 :=
    (Finset.card_insert_le _ _).trans (by omega)
  exact (Group.rank_le hgenT).trans (hcard.le.trans (Nat.pow_le_pow_left hc _))

/-- A subgroup of a fixed finite power has a bound depending only on the
factor rank, nilpotency class and number of coordinates. -/
theorem finite_power_nilpotent_subgroup_bounds {ι B : Type*} [Fintype ι] [Group B] [Finite B]
    [Group.IsNilpotent B] (r c : ℕ) (hr : Group.rank B ≤ r) (hc : Group.nilpotencyClass B ≤ c)
    (U : Subgroup (ι → B)) :
    Group.rank U ≤ ∑ i ∈ Finset.range c, ((r+1)^Fintype.card ι)^(i+1) ∧
    Group.nilpotencyClass U ≤ c := by
  have hclass : Group.nilpotencyClass (ι → B) ≤ c := by
    rw [Group.nilpotencyClass_pi]
    exact Finset.sup_le (fun _ _ => hc)
  exact ⟨nilpotent_subgroup_rank_bound _ c (finite_power_group_rank_bound r hr) hclass U,
    (Subgroup.nilpotencyClass_le U).trans hclass⟩

end DirectedCycles
