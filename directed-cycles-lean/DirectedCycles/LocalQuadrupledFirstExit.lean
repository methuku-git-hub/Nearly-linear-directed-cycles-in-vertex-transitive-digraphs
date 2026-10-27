module

public import DirectedCycles.LocalDoubledFirstExit

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Extending the actual first-exit segment a second time supplies the
fourfold domains needed by bounded signed corrections in the lifting proof. -/
theorem local_approximate_quadrupled_first_exit {G : Type*} (L : LocalGroupAlgebra G)
    {K : ℕ} {A : Finset G} (hA : IsLocalFiniteApproximateGroup L K A)
    {u : G} (hu : u ∈ A) (hupos : 0 < L.escapeNorm (A : Set G) u) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ p : L.PowerSegment u (4*N),
      (∀ n < N, p.power n ∈ A) ∧ p.power N ∉ A ∧
      L.escapeNorm A u = 1/(N : ℝ) ∧
      (∀ n ≤ 4*N, p.power n ∈ L.wordPower (A : Set G) 8) := by
  obtain ⟨N,hN,q,hprev,hexit,hnorm,hmem⟩ := local_approximate_doubled_first_exit L hA hu hupos
  have hA4one : L.one ∈ L.wordPower (A : Set G) 4 := by
    apply L.wordPower_subset_wordPower hA.one_mem hA.allProducts (by omega : 1 ≤ 4) (by omega)
    rw [L.wordPower_one]
    exact hA.one_mem
  obtain ⟨p,hmatch,hp⟩ := q.exists_double L (by omega) hA4one hmem
    (hA.allProducts.wordPower L (by omega : 4*4 ≤ 200))
  let p' : L.PowerSegment u (4*N) := ⟨p.power,fun n hn => p.product n (by omega)⟩
  refine ⟨N,hN,p',?_,?_,hnorm,?_⟩
  · intro n hn
    change p.power n ∈ A
    rw [hmatch n (by omega)]
    exact hprev n hn
  · change p.power N ∉ A
    rw [hmatch N (by omega)]
    exact hexit
  · intro n hn
    exact L.wordPower_wordPower_subset hA.allProducts 4 2 (by omega) (hp n (by omega))
end DirectedCycles
