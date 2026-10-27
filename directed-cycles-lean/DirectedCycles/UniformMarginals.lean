module

public import DirectedCycles.UniformFinite

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Iterated averaging on a finite product. -/
theorem uniformAverage_prod {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (f : Ω → Λ → ℝ) :
    uniformAverage (fun p : Ω × Λ => f p.1 p.2) =
      uniformAverage (fun ω => uniformAverage (f ω)) := by
  simp only [uniformAverage, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

/-- A coordinate of the finite uniform product is itself uniform. -/
theorem uniformAverage_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (β : I → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (i : I) (f : β i → ℝ) :
    uniformAverage (fun ω : ∀ j, β j => f (ω i)) = uniformAverage f := by
  let R := ∀ j : {j // j ≠ i}, β j
  let e : (∀ j, β j) ≃ β i × R := Equiv.piSplitAt i β
  calc uniformAverage (fun ω : ∀ j, β j => f (ω i)) =
      uniformAverage (fun p : β i × R => f ((e.symm p) i)) :=
        (uniformAverage_equiv e.symm (fun ω => f (ω i))).symm
    _ = uniformAverage (fun p : β i × R => f p.1) := by
      congr 1
      funext p
      simp [e, Equiv.piSplitAt]
    _ = uniformAverage f := uniformAverage_prod_left f

/-- Two distinct coordinates have the uniform product law, for arbitrary
joint functions rather than just products of separate functions. -/
theorem uniformAverage_two_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (β : I → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (i j : I) (hji : j ≠ i) (f : β i → β j → ℝ) :
    uniformAverage (fun ω : ∀ r, β r => f (ω i) (ω j)) =
      uniformAverage (fun p : β i × β j => f p.1 p.2) := by
  let R := ∀ r : {r // r ≠ i}, β r
  let e : (∀ r, β r) ≃ β i × R := Equiv.piSplitAt i β
  let j' : {r // r ≠ i} := ⟨j, hji⟩
  calc uniformAverage (fun ω : ∀ r, β r => f (ω i) (ω j)) =
      uniformAverage (fun p : β i × R => f ((e.symm p) i) ((e.symm p) j)) :=
        (uniformAverage_equiv e.symm (fun ω => f (ω i) (ω j))).symm
    _ = uniformAverage (fun p : β i × R => f p.1 (p.2 j')) := by
      congr 1
      funext p
      simp [e, Equiv.piSplitAt, hji, j']
    _ = uniformAverage (fun x : β i => uniformAverage (fun r : R => f x (r j'))) :=
      uniformAverage_prod (fun (x : β i) (r : R) => f x (r j'))
    _ = uniformAverage (fun x : β i => uniformAverage (f x)) := by
      congr 1
      funext x
      exact uniformAverage_coordinate (fun r : {r // r ≠ i} => β r) j' (f x)
    _ = uniformAverage (fun p : β i × β j => f p.1 p.2) := (uniformAverage_prod f).symm

end DirectedCycles
