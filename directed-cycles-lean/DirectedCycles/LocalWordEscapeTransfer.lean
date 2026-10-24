import DirectedCycles.LocalWordEscape
import DirectedCycles.LocalEscapeEstimateTransfer
import DirectedCycles.LocalUltraproductProductExistence

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- The undefined-word convention is also preserved by the ultralimit.
Definedness is transferred as an existence statement with a product value. -/
theorem localUltra_wordEscape_tendsto (A : ∀ i, Set (G i))
    (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i) (l : List (∀ i, G i)) :
    Filter.Tendsto (fun i => (L i).wordEscape (A i) (l.map (fun a => a i))) (U : Filter ι)
      (𝓝 ((localUltraAlgebra (U : Filter ι) G L).wordEscape
        (localUltraSet (U : Filter ι) G A) (l.map (localUltraMk (U : Filter ι) G)))) := by
  let M := localUltraAlgebra (U : Filter ι) G L
  let B := localUltraSet (U : Filter ι) G A
  by_cases hex : ∃ x, M.Product (l.map (localUltraMk (U : Filter ι) G)) x
  · obtain ⟨x,hx⟩ := hex
    obtain ⟨a,rfl⟩ := Quotient.exists_rep x
    rw [M.wordEscape_of_product hx]
    have hp := (localUltraProduct_mk_iff (U : Filter ι) G L l a).1 hx
    have he : (fun i => (L i).escapeNorm (A i) (a i)) =ᶠ[(U : Filter ι)]
        (fun i => (L i).wordEscape (A i) (l.map (fun a => a i))) :=
      hp.mono (fun i hi => ((L i).wordEscape_of_product hi).symm)
    exact (localUltra_escapeNorm_tendsto G L U A a hA).congr' he
  · rw [M.wordEscape_of_undefined hex]
    have hn : ∀ᶠ i in (U : Filter ι), ¬ ∃ x, (L i).Product (l.map (fun a => a i)) x := by
      apply (Ultrafilter.eventually_not).2
      intro h
      exact hex ((localUltra_exists_product_iff (U : Filter ι) G L l).2 h)
    have he : (fun _ : ι => (1 : ℝ)) =ᶠ[(U : Filter ι)]
        (fun i => (L i).wordEscape (A i) (l.map (fun a => a i))) :=
      hn.mono (fun i hi => ((L i).wordEscape_of_undefined hi).symm)
    exact (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => (1 : ℝ)) (U : Filter ι) (𝓝 1)).congr' he
end DirectedCycles
