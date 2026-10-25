module

public import DirectedCycles.RetainedPositions

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Successor in the actual cyclic order of retained positions. -/
def retainedNext {G : Type*} (data : List (ℕ × G)) (p : RetainedPosition data) : RetainedPosition data :=
  if hk : p.2.val+1 < (data[p.1.val]).1+1 then ⟨p.1,⟨p.2.val+1,hk⟩⟩
  else ⟨finRotate data.length p.1,⟨0,by omega⟩⟩

/-- The cyclic retained successor has the next numeric index, including the
last-to-first transition. -/
theorem retainedNext_index {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (p : RetainedPosition data) :
    (retainedPositionEquiv a D data (retainedNext data p)).val =
      ((retainedPositionEquiv a D data p).val+1)%(cyclicBaselineWord a D data).length := by
  rcases p with ⟨i,k⟩
  by_cases hk : k.val+1 < (data[i.val]).1+1
  · have hn : retainedNext data ⟨i,k⟩ = ⟨i,⟨k.val+1,hk⟩⟩ := by
      unfold retainedNext
      rw [dite_eq_left hk]
    rw [hn,retainedPositionEquiv_val,retainedPositionEquiv_val]
    have hb := (retainedPositionEquiv a D data ⟨i,⟨k.val+1,hk⟩⟩).isLt
    rw [retainedPositionEquiv_val] at hb
    rw [Nat.add_assoc,Nat.mod_eq_of_lt hb]
  · have hkval : k.val = (data[i.val]).1 := by have := k.isLt; omega
    have hn : retainedNext data ⟨i,k⟩ = ⟨finRotate data.length i,⟨0,by omega⟩⟩ := by
      unfold retainedNext
      rw [dite_eq_right hk]
    rw [hn,retainedPositionEquiv_val,retainedPositionEquiv_val,hkval,Nat.add_zero]
    have hsum : ((data.take (i.val+1)).map (fun z => z.1+1)).sum =
        ((data.take i.val).map (fun z => z.1+1)).sum + ((data[i.val]).1+1) := by
      rw [← List.take_concat_get' data i.val i.isLt,List.map_append,List.sum_append,
        List.map_singleton,List.sum_singleton]
    let : NeZero data.length := ⟨by have := i.isLt; omega⟩
    by_cases hi : i.val+1 < data.length
    · have hrot : (finRotate data.length i).val = i.val+1 := by
        rw [finRotate_apply]
        simp only [Fin.val_add,Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < data.length by omega),Nat.mod_eq_of_lt hi]
      rw [hrot,hsum,← Nat.add_assoc]
      have hb := (retainedPositionEquiv a D data ⟨finRotate data.length i,⟨0,by omega⟩⟩).isLt
      simp only [retainedPositionEquiv_val,hrot,Nat.add_zero,hsum,← Nat.add_assoc] at hb
      rw [Nat.mod_eq_of_lt hb]
    · have hit : i.val+1 = data.length := by have := i.isLt; omega
      have hrot : (finRotate data.length i).val = 0 := by
        rw [finRotate_apply]
        simp only [Fin.val_add,Fin.val_one']
        by_cases hlen : data.length = 1
        · have hi0 : i.val = 0 := by omega
          simp only [hlen,hi0,Nat.mod_one]
        · rw [Nat.mod_eq_of_lt (show 1 < data.length by omega),hit,Nat.mod_self]
      rw [hit,List.take_length] at hsum
      rw [hrot,List.take_zero,List.map_nil,List.sum_nil,cyclicBaselineWord_length,
        Nat.add_assoc,← hsum,Nat.mod_self]

/-- A compressed connector always ends at level zero of the next quotient
position, including the final connector. -/
theorem retainedNext_connector_level {G : Type*} (data : List (ℕ × G))
    (p : RetainedPosition data) (hp : p.2.val = (data[p.1.val]).1) :
    (retainedNext data p).2.val = 0 := by
  have hn : ¬ p.2.val+1 < (data[p.1.val]).1+1 := by omega
  unfold retainedNext
  rw [dite_eq_right hn]

end DirectedCycles
