import DirectedCycles.LocalUltraproductDomain
import Mathlib.Order.Filter.Ultrafilter.Basic

set_option autoImplicit false
open Filter
namespace DirectedCycles

theorem localUltraSet_inter {ι : Type*} (f : Filter ι) (G : ι → Type*) 
    (A B : ∀ i, Set (G i)) :
    localUltraSet f G (fun i => A i ∩ B i) = localUltraSet f G A ∩ localUltraSet f G B := by
  ext z
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  simp only [Set.mem_inter_iff,localUltraMk_mem_iff,Filter.eventually_and]

theorem localUltraSet_compl {ι : Type*} (u : Ultrafilter ι) (G : ι → Type*) 
    (A : ∀ i, Set (G i)) :
    localUltraSet (u : Filter ι) G (fun i => (A i)ᶜ) = (localUltraSet (u : Filter ι) G A)ᶜ := by
  ext z
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  simp only [Set.mem_compl_iff,localUltraMk_mem_iff,Ultrafilter.eventually_not]

theorem localUltraSet_subset_iff_eventually {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) (e : ∀ i, G i) (A B : ∀ i, Set (G i)) :
    localUltraSet (u : Filter ι) G A ⊆ localUltraSet (u : Filter ι) G B ↔
      ∀ᶠ i in (u : Filter ι), A i ⊆ B i := by
  classical
  constructor
  · intro h
    by_contra hnot
    have hbad : ∀ᶠ i in (u : Filter ι), ∃ x, x ∈ A i ∧ x ∉ B i := by
      simpa only [Set.not_subset] using (Ultrafilter.eventually_not.mpr hnot)
    let x : ∀ i, G i := fun i => if h : ∃ x, x ∈ A i ∧ x ∉ B i then Classical.choose h else e i
    have hmem : ∀ᶠ i in (u : Filter ι), x i ∈ A i ∧ x i ∉ B i := by
      filter_upwards [hbad] with i hi
      dsimp only [x]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    have hxA : localUltraMk (u : Filter ι) G x ∈ localUltraSet (u : Filter ι) G A :=
      (localUltraMk_mem_iff _ G A x).mpr (hmem.mono (fun _ hi => hi.1))
    have hxB := (localUltraMk_mem_iff _ G B x).mp (h hxA)
    obtain ⟨i,hi,hj⟩ := (hmem.and hxB).exists
    exact hi.2 hj
  · intro h z hz
    obtain ⟨x,hx,rfl⟩ := hz
    apply (localUltraMk_mem_iff _ G B x).2
    filter_upwards [h,hx] with i hi hxi
    exact hi hxi

theorem localUltraSet_eq_iff_eventually {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) (e : ∀ i, G i) (A B : ∀ i, Set (G i)) :
    localUltraSet (u : Filter ι) G A = localUltraSet (u : Filter ι) G B ↔
      ∀ᶠ i in (u : Filter ι), A i = B i := by
  rw [Set.Subset.antisymm_iff,localUltraSet_subset_iff_eventually u G e,localUltraSet_subset_iff_eventually u G e,
    ← Filter.eventually_and]
  simp only [Set.Subset.antisymm_iff]

end DirectedCycles
