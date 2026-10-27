module

public import DirectedCycles.FiniteApproximateCounterexamples
public import DirectedCycles.UltraproductApproximateGroups

@[expose] public section

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- Growing finite sets give an infinite internal set in a nonprincipal
ultraproduct. The proof constructs an explicit injection of the naturals. -/
theorem infinite_internal_set_of_growing_card (K : ℝ) (X : ℕ → FiniteApproximateExample K)
    (hcard : ∀ n, n+1 < Nat.card (X n).set) :
    Infinite (ultraSet (Filter.hyperfilter ℕ : Filter ℕ) (fun n => (X n).carrier) (fun n => (X n).set)) := by
  classical
  let G := fun n => (X n).carrier
  let A := fun n => (X n).set
  let f : Filter ℕ := Filter.hyperfilter ℕ
  let : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite _
  have hsize : ∀ i, i+2 ≤ Fintype.card (A i) := by
    intro i
    rw [← Nat.card_eq_fintype_card]
    exact hcard i
  let e : ∀ i, Fin (i+2) ↪ A i := fun i => {
    toFun := fun j => (Fintype.equivFin (A i)).symm ⟨j.val,j.isLt.trans_le (hsize i)⟩
    inj' := by
      intro a b hab
      apply Fin.ext
      exact congrArg (fun z : Fin (Fintype.card (A i)) => z.val)
        ((Fintype.equivFin (A i)).symm.injective hab) }
  let a : ℕ → ∀ i, G i := fun j i => if h : j < i+2 then (e i ⟨j,h⟩).val else 1
  have ha : ∀ j i, a j i ∈ A i := by
    intro j i
    dsimp [a]
    split
    · exact (e i _).property
    · exact (X i).approximate.one_mem
  let t : ℕ → ultraSet f G A := fun j =>
    ⟨ultraMk f G (a j),(ultraMk_mem_ultraSet_iff f G A (a j)).mpr (Eventually.of_forall (ha j))⟩
  have ht : Function.Injective t := by
    intro j k he
    have hv : ultraMk f G (a j) = ultraMk f G (a k) := congrArg Subtype.val he
    have hev := (ultraMk_eq_iff f G _ _).mp hv
    have hlarge : ∀ᶠ i in f, max j k ≤ i :=
      (eventually_ge_atTop (max j k)).filter_mono Nat.hyperfilter_le_atTop
    obtain ⟨i,hi,hji⟩ := (hev.and hlarge).exists
    have hj : j < i+2 := by omega
    have hk : k < i+2 := by omega
    have hab : (e i ⟨j,hj⟩).val = (e i ⟨k,hk⟩).val := by
      simpa only [a,dite_eq_left hj,dite_eq_left hk] using hi
    exact congrArg Fin.val ((e i).injective (Subtype.ext hab))
  exact Infinite.of_injective t ht

end DirectedCycles
