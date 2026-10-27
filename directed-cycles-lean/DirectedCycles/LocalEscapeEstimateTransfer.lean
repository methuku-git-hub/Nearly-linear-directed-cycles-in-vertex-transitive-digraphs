module

public import DirectedCycles.LocalUltraproductEscape

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Finite sums of actual component escape norms converge to the sum of the
actual local-ultraproduct escape norms. -/
theorem localUltra_escapeNorm_sum_tendsto (A : ∀ i, Set (G i))
    (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i) (l : List (∀ i, G i)) :
    Filter.Tendsto (fun i => (l.map (fun a => (L i).escapeNorm (A i) (a i))).sum) (U : Filter ι)
      (𝓝 ((l.map (fun a => (localUltraAlgebra (U : Filter ι) G L).escapeNorm
        (localUltraSet (U : Filter ι) G A) (localUltraMk (U : Filter ι) G a))).sum)) := by
  induction l with
  | nil =>
    simp only [List.map_nil,List.sum_nil]
    exact tendsto_const_nhds
  | cons a l ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (localUltra_escapeNorm_tendsto G L U A a hA).add ih

/-- A proved uniform finite-stage product estimate transfers to the genuine
local ultraproduct. This theorem does not assume that the finite-stage
analytic estimate itself has already been established. -/
theorem localUltra_escapeNorm_product_le (A : ∀ i, Set (G i))
    (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i) (B : ℝ)
    (hprod : ∀ᶠ i in (U : Filter ι), ∀ l : List (G i), ∀ x : G i,
      (L i).Product l x → (L i).escapeNorm (A i) x ≤ B*(l.map ((L i).escapeNorm (A i))).sum)
    (l : List (∀ i, G i)) (x : ∀ i, G i)
    (hx : (localUltraAlgebra (U : Filter ι) G L).Product
      (l.map (localUltraMk (U : Filter ι) G)) (localUltraMk (U : Filter ι) G x)) :
    (localUltraAlgebra (U : Filter ι) G L).escapeNorm
      (localUltraSet (U : Filter ι) G A) (localUltraMk (U : Filter ι) G x) ≤
      B*(l.map (fun a => (localUltraAlgebra (U : Filter ι) G L).escapeNorm
        (localUltraSet (U : Filter ι) G A) (localUltraMk (U : Filter ι) G a))).sum := by
  have hleft := localUltra_escapeNorm_tendsto G L U A x hA
  have hright := (localUltra_escapeNorm_sum_tendsto U G L A hA l).const_mul B
  apply le_of_tendsto_of_tendsto hleft hright
  have hp := (localUltraProduct_mk_iff (U : Filter ι) G L l x).1 hx
  filter_upwards [hprod,hp] with i hi hpi
  simpa only [List.map_map,Function.comp_def] using hi (l.map (fun a => a i)) (x i) hpi

/-- Vanishing component norms characterize zero norm in the local
ultraproduct. Eventual exact zero is a stronger, separate property. -/
theorem localUltra_escapeNorm_zero_iff (A : ∀ i, Set (G i)) (a : ∀ i, G i)
    (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i) :
    (localUltraAlgebra (U : Filter ι) G L).escapeNorm
      (localUltraSet (U : Filter ι) G A) (localUltraMk (U : Filter ι) G a) = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι), (L i).escapeNorm (A i) (a i) < ε := by
  have ht := localUltra_escapeNorm_tendsto G L U A a hA
  constructor
  · intro hz ε hε
    rw [hz] at ht
    have he := (Metric.tendsto_nhds.mp ht ε hε)
    filter_upwards [he,hA] with i hi hAi
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ((L i).escapeNorm_nonneg hAi (a i))] using hi
  · intro h
    have ht0 : Filter.Tendsto (fun i => (L i).escapeNorm (A i) (a i)) (U : Filter ι) (𝓝 (0 : ℝ)) := by
      apply Metric.tendsto_nhds.2
      intro ε hε
      filter_upwards [h ε hε,hA] with i hi hAi
      simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ((L i).escapeNorm_nonneg hAi (a i))] using hi
    exact tendsto_nhds_unique ht ht0
end DirectedCycles
