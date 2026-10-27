module

public import DirectedCycles.RetainedSuccessor
public import DirectedCycles.CyclicAuxiliaryGraph

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The standard finite-index equivalence is the natural residue-class map. -/
theorem zmod_finEquiv_apply (n : ℕ) [NeZero n] (i : Fin n) :
    (ZMod.finEquiv n).toEquiv i = (i.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    change i.val = i.val % (n+1)
    exact (Nat.mod_eq_of_lt i.isLt).symm

/-- Identify the actual cyclic layer with its quotient position and run level. -/
def retainedLayerEquiv {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (hne : data ≠ []) :
    RetainedPosition data ≃ ZMod (slotBaseline (cyclicLiftSlots a D data)).length := by
  let : NeZero (slotBaseline (cyclicLiftSlots a D data)).length :=
    ⟨Nat.ne_of_gt (cyclicLiftSlots_baseline_length_pos a D data hne)⟩
  exact (retainedPositionEquiv a D data).trans
    ((finCongr (congrArg List.length (cyclicLiftSlots_baseline a D data)).symm).trans
      (ZMod.finEquiv _).toEquiv)

theorem retainedLayerEquiv_apply {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (hne : data ≠ []) (p : RetainedPosition data) :
    retainedLayerEquiv a D data hne p = ((retainedPositionEquiv a D data p).val :
      ZMod (slotBaseline (cyclicLiftSlots a D data)).length) := by
  let : NeZero (slotBaseline (cyclicLiftSlots a D data)).length :=
    ⟨Nat.ne_of_gt (cyclicLiftSlots_baseline_length_pos a D data hne)⟩
  simp only [retainedLayerEquiv,Equiv.trans_apply,finCongr_apply,zmod_finEquiv_apply,Fin.val_cast]

theorem retainedLayerEquiv_val {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (hne : data ≠ []) (p : RetainedPosition data) :
    (retainedLayerEquiv a D data hne p).val = (retainedPositionEquiv a D data p).val := by
  let : NeZero (slotBaseline (cyclicLiftSlots a D data)).length :=
    ⟨Nat.ne_of_gt (cyclicLiftSlots_baseline_length_pos a D data hne)⟩
  rw [retainedLayerEquiv_apply,ZMod.val_natCast_of_lt]
  simpa only [cyclicLiftSlots_baseline] using (retainedPositionEquiv a D data p).isLt

/-- The list indexing and cyclic-layer indexing have exactly the same successor. -/
theorem retainedLayerEquiv_next {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (hne : data ≠ []) (p : RetainedPosition data) :
    retainedLayerEquiv a D data hne (retainedNext data p) =
      retainedLayerEquiv a D data hne p + 1 := by
  rw [retainedLayerEquiv_apply,retainedLayerEquiv_apply,retainedNext_index]
  have hlen := congrArg List.length (cyclicLiftSlots_baseline a D data)
  conv_lhs => arg 1; arg 2; rw [← hlen]
  rw [ZMod.natCast_mod,Nat.cast_add,Nat.cast_one]

/-- Reading a successor layer therefore gives the explicit retained successor. -/
theorem retainedLayerEquiv_symm_next {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (hne : data ≠ [])
    (z : ZMod (slotBaseline (cyclicLiftSlots a D data)).length) :
    (retainedLayerEquiv a D data hne).symm (z+1) =
      retainedNext data ((retainedLayerEquiv a D data hne).symm z) := by
  apply (retainedLayerEquiv a D data hne).injective
  rw [Equiv.apply_symm_apply,retainedLayerEquiv_next,Equiv.apply_symm_apply]

end DirectedCycles
