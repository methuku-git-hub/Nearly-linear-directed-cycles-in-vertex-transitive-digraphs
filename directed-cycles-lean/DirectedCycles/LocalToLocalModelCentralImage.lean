import DirectedCycles.LocalCentralSetUltraproduct
import DirectedCycles.LocalCentralSetHomImage
import DirectedCycles.LocalLieTargetEscapeNeighbourhood

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- The image of the actual component central sets is locally closed and
central on actual open target neighbourhoods. Both target neighbourhoods are
constructed by lifting finite power conditions into source escape bounds. -/
theorem local_to_local_model_central_image {H E : Type*}
    [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    {Q : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) Q)
    (A P : ∀ i, Set (G i)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hP : ∀ i, (L i).CentralLocalSet (P i) {x | (L i).escapeNorm (A i) x < a}
      {x | (L i).escapeNorm (A i) x < b})
    (hPA : ∀ i, P i ⊆ A i)
    (hA : (localUltraAlgebra (U : Filter ι) G L).one ∈ localUltraSet (U : Filter ι) G A)
    (hdom : ∀ x ∈ localUltraSet (U : Filter ι) G A, ∀ y ∈ localUltraSet (U : Filter ι) G A,
      (localUltraAlgebra (U : Filter ι) G L).Defined x y)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (W : Set H) (hWo : IsOpen W) (hW1 : Q.one ∈ W)
    (hsmall : ∀ z, π.toFun z ∈ W → z ∈ localUltraSet (U : Filter ι) G A)
    (hthick : ∀ y ∈ W, ∃ z, π.toFun z = y) :
    ∃ V S : Set H, IsOpen V ∧ Q.one ∈ V ∧ IsOpen S ∧ Q.one ∈ S ∧
      Q.CentralLocalSet (π.toFun '' localUltraSet (U : Filter ι) G P) V S := by
  obtain ⟨V,hVo,hV1,_,hVsmall⟩ := local_to_local_model_internal_escape_neighbourhood U G L D A hA hdom π W hWo hW1 hsmall ha
  obtain ⟨S,hSo,hS1,hSW,hSsmall⟩ := local_to_local_model_internal_escape_neighbourhood U G L D A hA hdom π W hWo hW1 hsmall hb
  have hPu := localUltra_centralLocalSet U G L P
    (fun i => {x | (L i).escapeNorm (A i) x < a}) (fun i => {x | (L i).escapeNorm (A i) x < b}) hP
  have hPAu : localUltraSet (U : Filter ι) G P ⊆ localUltraSet (U : Filter ι) G A := by
    rintro _ ⟨p,hp,rfl⟩
    exact (localUltraMk_mem_iff _ G A p).2 (hp.mono fun i hi => hPA i hi)
  refine ⟨V,S,hVo,hV1,hSo,hS1,hPu.hom_image π V S (fun x hx y hy => hdom x (hPAu hx) y (hPAu hy)) hVsmall ?_⟩
  intro y hy
  obtain ⟨z,hz⟩ := hthick y (hSW hy)
  exact ⟨z,hSsmall z (hz.symm ▸ hy),hz⟩
end DirectedCycles
