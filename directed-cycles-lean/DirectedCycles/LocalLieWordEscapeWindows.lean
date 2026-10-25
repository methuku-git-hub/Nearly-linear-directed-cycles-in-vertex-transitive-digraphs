module

public import DirectedCycles.LocalWordContainmentEscape
public import DirectedCycles.LieModelWordDomains

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [Group H] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [LieGroup 𝓘(ℝ,E) ∞ H]

/-- Every sufficiently small exponential source window has prescribed
long word domains and arbitrarily small component escape, uniformly over the
chosen internal representatives. The radius is constructed from the model. -/
theorem exists_lie_model_word_escape_radius
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (A : ∀ i, Set (G i))
    (hA1 : (localUltraAlgebra (U : Filter ι) G L).one ∈ localUltraSet (U : Filter ι) G A)
    (hdom : ∀ x ∈ localUltraSet (U : Filter ι) G A, ∀ y ∈ localUltraSet (U : Filter ι) G A,
      (localUltraAlgebra (U : Filter ι) G L).Defined x y)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (W : Set H) (hW : W ∈ 𝓝 (1 : H))
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ localUltraSet (U : Filter ι) G A)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R → ∀ B : ∀ i, Set (G i),
      π.toFun '' localUltraSet (U : Filter ι) G B ⊆
        (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000 : ℝ)*r) →
      ∀ᶠ i in (U : Filter ι), (B i ⊆ A i) ∧ (L i).AllProductsDefined (B i) m ∧
        ∀ n ≤ m, ∀ x ∈ (L i).wordPower (B i) n, (L i).escapeNorm (A i) x < ε := by
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
  obtain ⟨R,hR,hwords⟩ := exists_lie_model_word_domain_radius (E := E)
    (localUltraAlgebra (U : Filter ι) G L) (localUltraSet (U : Filter ι) G A) hA1 hdom π W hW hsmall (m*(N+1))
  refine ⟨R,hR,?_⟩
  intro r hr hrR B hB
  obtain ⟨hBA,hBdom,hBAwords⟩ := hwords r hr hrR (localUltraSet (U : Filter ι) G B) hB
  have hsub := (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) B A).1 hBA
  have hdomains := (localUltra_allProductsDefined_iff U G L B (m*(N+1))).1 hBdom
  have hcontain := local_word_containment_eventually U G L A B (m*(N+1)) hBAwords
  filter_upwards [hsub,hdomains,hcontain] with i hi hdi hci
  refine ⟨hi,hdi.mono (L i) (Set.Subset.refl _) (by nlinarith : m ≤ m*(N+1)),?_⟩
  intro n hn x hx
  exact ((L i).escape_of_word_containment hdi hci n hn x hx).trans_lt hN
end DirectedCycles
