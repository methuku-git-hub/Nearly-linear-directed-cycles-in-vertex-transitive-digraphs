module

public import DirectedCycles.LocalFiniteEscapeNeighbourhoods
public import DirectedCycles.LocalProductDomainTransfer
public import DirectedCycles.LocalWordPowerTransfer
public import DirectedCycles.LocalInternalSetLogic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Long actual word containment bounds escape for every shorter word.
All intermediate powers are constructed inside the supplied word domain. -/
theorem escape_of_word_containment {A B : Set G} {m N : ℕ}
    (hdom : L.AllProductsDefined B (m*(N+1)))
    (hcontain : ∀ n ≤ m*(N+1), L.wordPower B n ⊆ A) :
    ∀ n ≤ m, ∀ x ∈ L.wordPower B n, L.escapeNorm A x ≤ 1/((N : ℝ)+1) := by
  intro n hn x hx
  apply L.escapeNorm_le_of_powers (n := N)
  intro j hj
  have hnj : n*j ≤ m*(N+1) := Nat.mul_le_mul hn (by omega)
  obtain ⟨y,hy,hp⟩ := L.powerIn_wordPower hdom hnj hx
  exact ⟨y,hcontain (n*j) hnj hy,hp⟩
end LocalGroupAlgebra

/-- A whole bounded family of internal word containments reflects at once
to an eventual bounded family of actual component containments. -/
theorem local_word_containment_eventually {ι : Type*} (U : Ultrafilter ι)
    (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i)) (A B : ∀ i, Set (G i)) (N : ℕ)
    (h : ∀ n ≤ N, (localUltraAlgebra (U : Filter ι) G L).wordPower (localUltraSet (U : Filter ι) G B) n ⊆
      localUltraSet (U : Filter ι) G A) :
    ∀ᶠ i in (U : Filter ι), ∀ n ≤ N, (L i).wordPower (B i) n ⊆ A i := by
  have hn : ∀ n : Fin (N+1), ∀ᶠ i in (U : Filter ι), (L i).wordPower (B i) n.val ⊆ A i := by
    intro n
    apply (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).1
    rw [← localUltra_wordPower]
    exact h n.val (by omega)
  exact (Filter.eventually_all.mpr hn).mono fun i hi n hn => hi ⟨n,by omega⟩
end DirectedCycles
