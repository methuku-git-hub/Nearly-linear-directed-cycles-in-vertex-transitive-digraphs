import DirectedCycles.CollisionSeparatedRuns

set_option autoImplicit false
namespace DirectedCycles

def runPrefixSum {ell : ℕ} (l : Fin ell → ℕ) (D : ℕ) (i : Fin (ell+1)) : ℕ :=
  ((List.ofFn (fun j => l j+D)).take i.val).sum

theorem runPrefixSum_step {ell : ℕ} (l : Fin ell → ℕ) (D : ℕ) (i : Fin ell) :
    runPrefixSum l D i.succ = runPrefixSum l D i.castSucc + (l i+D) := by
  have he := List.take_concat_get' (List.ofFn (fun j => l j+D)) i.val
    (by simpa only [List.length_ofFn] using i.isLt)
  have hs := congrArg List.sum he
  simpa only [runPrefixSum,Fin.val_succ,Fin.val_castSucc,List.sum_append,List.sum_singleton,
    List.getElem_ofFn] using hs.symm

theorem finRotate_previous_successor {ell : ℕ} (hell : 2 ≤ ell) (i : Fin ell)
    (hi : i.val+1 < ell) : (finRotate ell).symm ⟨i.val+1,hi⟩ = i := by
  apply (finRotate ell).injective
  rw [Equiv.apply_symm_apply]
  let : NeZero ell := ⟨by omega⟩
  apply Fin.ext
  simp [finRotate_apply,Fin.val_add,Nat.mod_eq_of_lt (show 1 < ell by omega),Nat.mod_eq_of_lt hi]

/-- The chosen residues agree with the actual accumulated fixed-run
prefixes, including the closing offset at index zero. -/
theorem run_prefix_end_residue (ell h D : ℕ) (hell : 2 ≤ ell) [NeZero h]
    (l : Fin ell → ℕ) (v : Fin ell → ZMod h) (ν : ZMod h)
    (hzero : v ((finRotate ell).symm ⟨0,by omega⟩)+(D : ZMod h)+ν = 0)
    (hl : ∀ i : Fin ell, (l i : ZMod h) =
      v i-v ((finRotate ell).symm i)-(D : ZMod h)-(if i.val = 0 then ν else 0)) :
    ∀ i : Fin ell, (runPrefixSum l D i.castSucc : ZMod h)+(l i : ZMod h) = v i := by
  have hall : ∀ n : ℕ, ∀ hn : n < ell,
      (runPrefixSum l D (⟨n,hn⟩ : Fin ell).castSucc : ZMod h)+(l ⟨n,hn⟩ : ZMod h) = v ⟨n,hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      simp only [runPrefixSum,Fin.val_castSucc,List.take_zero,List.sum_nil,Nat.cast_zero,zero_add]
      rw [hl]
      simp only [ite_true]
      have hz := hzero
      linear_combination -hz
    | succ n ih =>
      intro hn
      have hn' : n < ell := by omega
      have he : (⟨n+1,hn⟩ : Fin ell).castSucc = (⟨n,hn'⟩ : Fin ell).succ := Fin.ext rfl
      rw [he,runPrefixSum_step]
      push_cast
      have hi := ih hn'
      rw [hl ⟨n+1,hn⟩,finRotate_previous_successor hell ⟨n,hn'⟩ hn]
      simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,sub_zero]
      linear_combination hi
  exact fun i => hall i.val i.isLt

end DirectedCycles
