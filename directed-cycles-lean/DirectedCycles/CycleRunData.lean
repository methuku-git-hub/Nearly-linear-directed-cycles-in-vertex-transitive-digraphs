module

public import DirectedCycles.CayleyCycleLabels
public import DirectedCycles.ConnectorPositions

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- Run lengths paired, in order, with the original quotient-cycle labels. -/
def cycleRunData {G : Type*} {ell : ℕ} (l : Fin ell → ℕ) (s : Fin ell → G) : List (ℕ × G) :=
  List.ofFn (fun i => (l i,s i))

@[simp] theorem cycleRunData_length {G : Type*} {ell : ℕ}
    (l : Fin ell → ℕ) (s : Fin ell → G) : (cycleRunData l s).length = ell := List.length_ofFn

@[simp] theorem cycleRunData_snd {G : Type*} {ell : ℕ}
    (l : Fin ell → ℕ) (s : Fin ell → G) : (cycleRunData l s).map Prod.snd = List.ofFn s := by
  simp only [cycleRunData,List.map_ofFn,Function.comp_def]

@[simp] theorem cycleRunData_sum {G : Type*} {ell : ℕ}
    (l : Fin ell → ℕ) (s : Fin ell → G) (t : ℕ) :
    ((cycleRunData l s).map (fun z => z.1+t)).sum = ∑ i, (l i+t) := by
  simp only [cycleRunData,List.map_ofFn,Function.comp_def,List.sum_ofFn]

@[simp] theorem cycleRunData_get {G : Type*} {ell : ℕ}
    (l : Fin ell → ℕ) (s : Fin ell → G) (i : Fin (cycleRunData l s).length) :
    (cycleRunData l s)[i.val] =
      (l ⟨i.val,by simpa only [cycleRunData_length] using i.isLt⟩,
       s ⟨i.val,by simpa only [cycleRunData_length] using i.isLt⟩) := by
  simp only [cycleRunData,List.getElem_ofFn]

/-- The inserted run-length data preserves the distinct quotient vertices of
the input cycle, after the proved translation to the identity. -/
theorem cycleRunData_prefix_injective {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (S : Set Q) (C : Cycle (CayleyDigraph S))
    (l : Fin C.length → ℕ) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*q (s i)) :
    Function.Injective (fun i : Fin (cycleRunData l s).length =>
      q (cycleLabelPrefixes (cycleRunData l s) i.castSucc)) := by
  intro i j he
  have hi : i.val < C.length := by simpa only [cycleRunData_length] using i.isLt
  have hj : j.val < C.length := by simpa only [cycleRunData_length] using j.isLt
  change q (((cycleRunData l s).map Prod.snd).take i.val).prod =
    q (((cycleRunData l s).map Prod.snd).take j.val).prod at he
  rw [cycleRunData_snd] at he
  have hpi := cayley_cycle_prefixes q S C s hstep ⟨i.val,hi⟩
  have hpj := cayley_cycle_prefixes q S C s hstep ⟨j.val,hj⟩
  change q ((List.ofFn s).take i.val).prod = _ at hpi
  change q ((List.ofFn s).take j.val).prod = _ at hpj
  rw [hpi,hpj] at he
  have hij := C.vertex.injective (mul_left_cancel he)
  exact Fin.ext (congrArg (fun z : Fin C.length => z.val) hij)

end DirectedCycles
