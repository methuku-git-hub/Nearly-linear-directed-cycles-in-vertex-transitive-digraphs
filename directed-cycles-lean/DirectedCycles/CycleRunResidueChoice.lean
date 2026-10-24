import DirectedCycles.ClosingResidueOffsets
import DirectedCycles.CollisionSeparatedRuns

set_option autoImplicit false
namespace DirectedCycles

theorem finRotate_no_fixed (ell : ℕ) (hell : 2 ≤ ell) (i : Fin ell) : finRotate ell i ≠ i := by
  let : NeZero ell := ⟨by omega⟩
  intro he
  rw [finRotate_apply] at he
  have h1 : (1 : Fin ell) = 0 := add_left_cancel (he.trans (add_zero i).symm)
  have hv := congrArg Fin.val h1
  change 1 % ell = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

theorem finRotate_previous_no_fixed (ell : ℕ) (hell : 2 ≤ ell) (i : Fin ell) :
    (finRotate ell).symm i ≠ i := by
  intro he
  have hh := congrArg (finRotate ell) he
  rw [Equiv.apply_symm_apply] at hh
  exact finRotate_no_fixed ell hell i hh.symm

/-- The run selection in the indexing and integer-congruence format
used by the actual cyclic-lift construction. -/
theorem choose_cycle_return_runs {K H : Type*} [Group H] [Fintype K]
    (ell h q D : ℕ) (hell : 2 ≤ ell) [NeZero h] (hh : 8*(q+1)*(D+1) < h)
    (hK : Fintype.card K ≤ q) (start finish : Fin ell ↪ H) (label : K → H)
    (e : RightCollision start finish label → ZMod h) (ν : ℤ) :
    ∃ v : Fin ell → ZMod h, ∃ l : Fin ell → ℕ,
      (∀ i, D ≤ l i ∧ (h+7)/8 ≤ l i ∧ l i ≤ h-2*D-2) ∧
      ((h : ℤ) ∣ ((∑ i, (l i+D) : ℕ) : ℤ)+ν) ∧
      (ell*h ≤ 8*∑ i,(l i+1)) ∧
      (∀ i, (runPrefixSum l D i.castSucc : ZMod h)+(l i : ZMod h) = v i) ∧
      (∀ i, (l i : ZMod h) = v i-v ((finRotate ell).symm i)-(D : ZMod h)-
        (if i.val = 0 then (ν : ZMod h) else 0)) ∧
      (∀ c : RightCollision start finish label,
        v c.val.2.2-v c.val.2.1 ∉ collisionForbiddenResidues h D (e c)) := by
  let νs := fun i : Fin ell => if i.val = 0 then (ν : ZMod h) else 0
  obtain ⟨v,l,hzero,hl,hbounds,hclose,hlen,havoid⟩ := choose_collision_separated_runs h q D hh hK
    (finRotate ell).symm (finRotate_previous_no_fixed ell hell) start finish label e νs ⟨0,by omega⟩
  have hli : ∀ i : Fin ell, (l i : ZMod h) =
      v i-v ((finRotate ell).symm i)-(D : ZMod h)-(if i.val = 0 then (ν : ZMod h) else 0) := by
    intro i
    rw [hl,ZMod.natCast_zmod_val]
    dsimp only [νs]
    abel
  have hz : v ((finRotate ell).symm ⟨0,by omega⟩)+(D : ZMod h)+(ν : ZMod h) = 0 := by
    simpa only [νs,ite_true] using hzero
  have hc : (∑ i, ((l i : ZMod h)+(D : ZMod h)))+(ν : ZMod h) = 0 := by
    rw [sum_closing_offset ell (by omega)] at hclose
    exact hclose
  refine ⟨v,l,hbounds,run_closure_integer_divisibility ell h D l ν hc,?_,
    run_prefix_end_residue ell h D hell l v ν hz hli,hli,havoid⟩
  simpa only [Fintype.card_fin] using hlen

end DirectedCycles
