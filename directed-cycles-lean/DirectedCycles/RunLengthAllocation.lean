module

public import DirectedCycles.Basic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- Two positions suffice to absorb any decrease up to twice their capacity. -/
theorem two_position_allocation (ell cap t : ℕ) (hell : 2 ≤ ell) (ht : t ≤ 2*cap) :
    ∃ d : Fin ell → ℕ, (∀ i, d i ≤ cap) ∧ (∑ i, d i) = t := by
  classical
  let i0 : Fin ell := ⟨0,by omega⟩
  let i1 : Fin ell := ⟨1,by omega⟩
  have hne : i0 ≠ i1 := by intro h; have h' := congrArg Fin.val h; dsimp [i0,i1] at h'; omega
  let u := min cap t
  let v := t-u
  have hu : u ≤ cap := Nat.min_le_left _ _
  have hut : u ≤ t := Nat.min_le_right _ _
  have hv : v ≤ cap := by dsimp [v,u]; omega
  let d : Fin ell → ℕ := fun i => (if i=i0 then u else 0)+(if i=i1 then v else 0)
  refine ⟨d,?_,?_⟩
  · intro i
    by_cases h0 : i=i0
    · have h1 : i ≠ i1 := by simpa only [h0] using hne
      simpa only [d,h0,h1,hne,ite_true,ite_false,add_zero] using hu
    · by_cases h1 : i=i1
      · simpa only [d,h0,h1,hne.symm,ite_true,ite_false,zero_add] using hv
      · simp only [d,h0,h1,ite_false,zero_add]; omega
  · simp only [d,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact Nat.add_sub_of_le hut

/-- The total retained-position lower bound after a decrease smaller than h. -/
theorem run_length_total_bound (ell h D upper T t : ℕ) (hell : 2 ≤ ell)
    (hh : 8*D+4 < h) (hupper : upper+2*D+2 = h)
    (ht : t < h) (hT : T+t = ell*(upper+1)) :
    (ell : ℝ)*h/4 < T := by
  have hell' : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hh' : 8*(D : ℝ)+4 < h := by exact_mod_cast hh
  have hupper' : (upper : ℝ)+2*D+2 = h := by exact_mod_cast hupper
  have ht' : (t : ℝ) ≤ h-1 := by
    have h' : (t : ℝ)+1 ≤ h := by exact_mod_cast (show t+1 ≤ h by omega)
    linarith
  have hT' : (T : ℝ)+t = ell*(upper+1) := by exact_mod_cast hT
  have hm := mul_nonneg (sub_nonneg.mpr hell')
    (show (0 : ℝ) ≤ 3*upper-2*D+2 by nlinarith)
  nlinarith

end DirectedCycles
