import DirectedCycles.StrongLocalCentralElement
import DirectedCycles.LocalFirstExitSegment
import DirectedCycles.LocalPowerSegmentDouble
import DirectedCycles.LocalWordPowerIteration

set_option autoImplicit false
namespace DirectedCycles

/-- A finite strong local NSS group supplies the least-escape generator and
a segment through twice its first exit. Earlier values stay in A; the entire
doubled segment stays in A^4, with all bracketings actually defined. -/
theorem strong_local_central_segment (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G) (A : Finset G),
        IsStrongLocalFiniteApproximateGroup L K A → L.DivisionClosed → L.Reversible →
        L.IsNSS (A : Set G) → (∃ g ∈ A, g ≠ L.one) →
        ∃ u ∈ A, u ≠ L.one ∧ ∃ N : ℕ, 2 ≤ N ∧ ∃ p : L.PowerSegment u (2*N),
          (∀ n < N, p.power n ∈ A) ∧ p.power N ∉ A ∧
          L.escapeNorm A u = 1/(N : ℝ) ∧
          (∀ v ∈ A, v ≠ L.one → L.escapeNorm A u ≤ L.escapeNorm A v) ∧
          (∀ x, L.escapeNorm A x < δ → L.Commute x u) ∧
          (∀ n ≤ 2*N, p.power n ∈ L.wordPower (A : Set G) 4) := by
  obtain ⟨δ,hδ,hδhalf,hcent⟩ := strong_local_central_element K
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro G _ L A hA hd hr hNSS hne
  obtain ⟨u,hu,hu1,hupos,hmin,hcentral,_⟩ := hcent G L A hA hd hr hNSS hne
  obtain ⟨N,hN,q,hout,hprev,hend,hnorm⟩ := L.exists_first_exit_segment hA.approximate.one_mem hu
    (hA.approximate.allProducts.mono L (Set.Subset.refl _) (by omega : 2 ≤ 200)) hupos
  have hN2 : 2 ≤ N := by
    by_contra h
    have he : N = 1 := by omega
    have hqN : q.power N = u := by simpa only [he] using q.one (by omega)
    exact hout (hqN.symm ▸ hu)
  have hsub : (A : Set G) ⊆ L.wordPower (A : Set G) 2 := by
    intro x hx
    apply L.wordPower_subset_wordPower hA.approximate.one_mem hA.approximate.allProducts
      (by omega : 1 ≤ 2) (by omega)
    simpa only [L.wordPower_one] using hx
  have hqmem : ∀ n ≤ N, q.power n ∈ L.wordPower (A : Set G) 2 := by
    intro n hn
    by_cases he : n = N
    · exact he ▸ hend
    · exact hsub (hprev n (by omega))
  have hdom : L.AllProductsDefined (L.wordPower (A : Set G) 2) 4 :=
    hA.approximate.allProducts.wordPower L (by omega : 2*4 ≤ 200)
  obtain ⟨p,hmatch,hmem⟩ := q.exists_double L (by omega) (hsub hA.approximate.one_mem) hqmem hdom
  refine ⟨u,hu,hu1,N,hN2,p,?_,?_,hnorm,hmin,hcentral,?_⟩
  · intro n hn
    rw [hmatch n hn.le]
    exact hprev n hn
  · rw [hmatch N le_rfl]
    exact hout
  · intro n hn
    exact L.wordPower_wordPower_subset hA.approximate.allProducts 2 2 (by omega) (hmem n hn)
end DirectedCycles
