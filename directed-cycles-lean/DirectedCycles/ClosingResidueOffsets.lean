import DirectedCycles.CyclicResiduePowers
import DirectedCycles.RunPrefixResidues

set_option autoImplicit false
namespace DirectedCycles

theorem finRotate_previous_zero (ell : ℕ) (hell : 2 ≤ ell) :
    (finRotate ell).symm ⟨0,by omega⟩ = ⟨ell-1,by omega⟩ := by
  apply (finRotate ell).injective
  rw [Equiv.apply_symm_apply]
  let : NeZero ell := ⟨by omega⟩
  apply Fin.ext
  have he : ell-1+1 = ell := by omega
  simp [finRotate_apply,Fin.val_add,Nat.mod_eq_of_lt (show 1 < ell by omega),he]

/-- The terminal prefix is retained at the closing connector. Its
voltage is absorbed only in the offset of the initial run. -/
theorem cyclic_prefix_finish_offsets {Q : Type*} [Group Q]
    (a : Q) (ell : ℕ) (hell : 2 ≤ ell) (g : Fin (ell+1) → Q)
    (ν : ZMod (orderOf a)) (hzero : g 0 = 1) (hlast : g (Fin.last ell) = residuePower a ν) :
    ∀ i : Fin ell,
      g (((finRotate ell).symm i).succ) =
        residuePower a (if i.val = 0 then ν else 0)*g i.castSucc := by
  intro i
  by_cases hi : i.val = 0
  · have hei : i = ⟨0,by omega⟩ := Fin.ext hi
    rw [hei,finRotate_previous_zero ell hell]
    have he : (⟨ell-1,by omega⟩ : Fin ell).succ = Fin.last ell := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_last]
      omega
    simp only [he,ite_true,hlast]
    change residuePower a ν = residuePower a ν*g 0
    rw [hzero,mul_one]
  · have hn : i.val-1 < ell := by omega
    have hni : i.val-1+1 < ell := by omega
    have hj := finRotate_previous_successor hell (⟨i.val-1,hn⟩ : Fin ell) hni
    have he : (⟨i.val-1+1,hni⟩ : Fin ell) = i := by
      apply Fin.ext
      change i.val-1+1 = i.val
      omega
    rw [he] at hj
    rw [hj,ite_eq_right hi,residuePower_zero,one_mul]
    apply congrArg g
    apply Fin.ext
    simp only [Fin.val_succ,Fin.val_castSucc]
    omega

theorem sum_closing_offset {A : Type*} [AddCommMonoid A] (ell : ℕ) (hell : 0 < ell) (ν : A) :
    (∑ i : Fin ell, if i.val = 0 then ν else 0) = ν := by
  classical
  rw [Finset.sum_eq_single (⟨0,hell⟩ : Fin ell)]
  · simp
  · intro i _ hi
    have hv : i.val ≠ 0 := fun he => hi (Fin.ext he)
    exact ite_eq_right hv
  · simp

theorem run_closure_integer_divisibility (ell h D : ℕ) [NeZero h]
    (l : Fin ell → ℕ) (ν : ℤ)
    (hc : (∑ i, ((l i : ZMod h)+(D : ZMod h)))+(ν : ZMod h) = 0) :
    (h : ℤ) ∣ ((∑ i, (l i+D) : ℕ) : ℤ)+ν := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  exact hc

end DirectedCycles
