import DirectedCycles.UltraproductInternalSets

set_option autoImplicit false
open Filter
namespace DirectedCycles

theorem ultraSet_inter {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A B : ∀ i, Set (G i)) :
    ultraSet f G (fun i => A i ∩ B i) = ultraSet f G A ∩ ultraSet f G B := by
  ext z
  obtain ⟨x,rfl⟩ := ultraMk_surjective f G z
  simp only [Set.mem_inter_iff,ultraMk_mem_ultraSet_iff,Filter.eventually_and]

theorem ultraSet_compl {ι : Type*} (u : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) :
    ultraSet (u : Filter ι) G (fun i => (A i)ᶜ) = (ultraSet (u : Filter ι) G A)ᶜ := by
  ext z
  obtain ⟨x,rfl⟩ := ultraMk_surjective (u : Filter ι) G z
  simp only [Set.mem_compl_iff,ultraMk_mem_ultraSet_iff,Ultrafilter.eventually_not]

theorem ultraSet_subset_iff_eventually {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (A B : ∀ i, Set (G i)) :
    ultraSet (u : Filter ι) G A ⊆ ultraSet (u : Filter ι) G B ↔
      ∀ᶠ i in (u : Filter ι), A i ⊆ B i := by
  classical
  constructor
  · intro h
    by_contra hnot
    have hbad : ∀ᶠ i in (u : Filter ι), ∃ x, x ∈ A i ∧ x ∉ B i := by
      simpa only [Set.not_subset] using (Ultrafilter.eventually_not.mpr hnot)
    let x : ∀ i, G i := fun i => if h : ∃ x, x ∈ A i ∧ x ∉ B i then Classical.choose h else 1
    have hmem : ∀ᶠ i in (u : Filter ι), x i ∈ A i ∧ x i ∉ B i := by
      filter_upwards [hbad] with i hi
      dsimp only [x]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    have hxA : ultraMk (u : Filter ι) G x ∈ ultraSet (u : Filter ι) G A :=
      (ultraMk_mem_ultraSet_iff _ G A x).mpr (hmem.mono (fun _ hi => hi.1))
    have hxB := (ultraMk_mem_ultraSet_iff _ G B x).mp (h hxA)
    obtain ⟨i,hi,hj⟩ := (hmem.and hxB).exists
    exact hi.2 hj
  · exact ultraSet_mono (u : Filter ι) G A B

theorem ultraSet_eq_iff_eventually {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (A B : ∀ i, Set (G i)) :
    ultraSet (u : Filter ι) G A = ultraSet (u : Filter ι) G B ↔
      ∀ᶠ i in (u : Filter ι), A i = B i := by
  rw [Set.Subset.antisymm_iff,ultraSet_subset_iff_eventually,ultraSet_subset_iff_eventually,
    ← Filter.eventually_and]
  simp only [Set.Subset.antisymm_iff]

end DirectedCycles
