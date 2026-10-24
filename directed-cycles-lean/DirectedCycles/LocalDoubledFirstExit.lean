import DirectedCycles.LocalApproximateGroups
import DirectedCycles.LocalFirstExitSegment
import DirectedCycles.LocalPowerSegmentDouble
import DirectedCycles.LocalWordPowerIteration
import DirectedCycles.LocalWordPowerMonotonicity

set_option autoImplicit false
namespace DirectedCycles

/-- Every positive-escape element of a finite local approximate group has
an actual doubled first-exit segment, with its endpoint and every value in
the certified fourth source power. Centrality and minimality are unnecessary. -/
theorem local_approximate_doubled_first_exit {G : Type*} (L : LocalGroupAlgebra G)
    {K : ℕ} {A : Finset G} (hA : IsLocalFiniteApproximateGroup L K A)
    {u : G} (hu : u ∈ A) (hupos : 0 < L.escapeNorm (A : Set G) u) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ p : L.PowerSegment u (2*N),
      (∀ n < N, p.power n ∈ A) ∧ p.power N ∉ A ∧
      L.escapeNorm A u = 1/(N : ℝ) ∧
      (∀ n ≤ 2*N, p.power n ∈ L.wordPower (A : Set G) 4) := by
  obtain ⟨N,hN,q,hout,hprev,hend,hnorm⟩ := L.exists_first_exit_segment hA.one_mem hu
    (hA.allProducts.mono L (Set.Subset.refl _) (by omega : 2 ≤ 200)) hupos
  have hN2 : 2 ≤ N := by
    by_contra h
    have he : N = 1 := by omega
    have hqN : q.power N = u := by simpa only [he] using q.one (by omega)
    exact hout (hqN.symm ▸ hu)
  have hsub : (A : Set G) ⊆ L.wordPower (A : Set G) 2 := by
    intro x hx
    apply L.wordPower_subset_wordPower hA.one_mem hA.allProducts
      (by omega : 1 ≤ 2) (by omega)
    simpa only [L.wordPower_one] using hx
  have hqmem : ∀ n ≤ N, q.power n ∈ L.wordPower (A : Set G) 2 := by
    intro n hn
    by_cases he : n = N
    · exact he ▸ hend
    · exact hsub (hprev n (by omega))
  have hdom : L.AllProductsDefined (L.wordPower (A : Set G) 2) 4 :=
    hA.allProducts.wordPower L (by omega : 2*4 ≤ 200)
  obtain ⟨p,hmatch,hmem⟩ := q.exists_double L (by omega) (hsub hA.one_mem) hqmem hdom
  refine ⟨N,hN2,p,?_,?_,hnorm,?_⟩
  · intro n hn
    rw [hmatch n hn.le]
    exact hprev n hn
  · rw [hmatch N le_rfl]
    exact hout
  · intro n hn
    exact L.wordPower_wordPower_subset hA.allProducts 2 2 (by omega) (hmem n hn)
end DirectedCycles
