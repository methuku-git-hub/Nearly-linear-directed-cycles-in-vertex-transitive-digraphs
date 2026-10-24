import DirectedCycles.StrongLocalUltraEscape
import DirectedCycles.LocalPowerTrappingTransfer
import DirectedCycles.LocalZeroEscapeNormal
import DirectedCycles.LocalProductDomainTransfer

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    [∀ i, Fintype (G i)] (A : ∀ i, Finset (G i)) {K : ℕ}

/-- The exact zero-escape subgroup of the actual local ultraproduct has an
actual NSS local quotient. This is an algebraic quotient of an external
zero-escape set; no internality or Lie-model compatibility is asserted here. -/
theorem strong_localUltra_zero_escape_nss
    (hd : ∀ᶠ i in (U : Filter ι), (L i).DivisionClosed)
    (hr : ∀ᶠ i in (U : Filter ι), (L i).Reversible)
    (hA : ∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (A i)) :
    let M := localUltraAlgebra (U : Filter ι) G L
    let B := localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
    let H := {x | M.escapeNorm B x = 0}
    let hD : M.DivisionClosed := localUltra_divisionClosed_eventually U G L hd
    let hR : M.Reversible := localUltra_reversible_eventually U G L hr
    ∃ W : M.NormalSubgroupWindow H (M.setMul H B),
      (W.congruence hD hR).algebra.IsNSS Set.univ := by
  dsimp only
  let M := localUltraAlgebra (U : Filter ι) G L
  let B := localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
  have hD : M.DivisionClosed := localUltra_divisionClosed_eventually U G L hd
  have hR : M.Reversible := localUltra_reversible_eventually U G L hr
  have hB1 : M.one ∈ B := (localUltraMk_mem_iff (U : Filter ι) G _ (fun i => (L i).one)).2
    (hA.mono fun _ hi => hi.approximate.one_mem)
  have hBi : ∀ x ∈ B, M.inv x ∈ B := by
    intro x hx
    obtain ⟨a,rfl⟩ := Quotient.exists_rep x
    have hm := (localUltraMk_mem_iff (U : Filter ι) G _ a).1 hx
    apply (localUltraMk_mem_iff (U : Filter ι) G _ (fun i => (L i).inv (a i))).2
    filter_upwards [hm,hA] with i hi hAi
    exact hAi.approximate.inv_mem _ hi
  have hdom : M.AllProductsDefined B 200 := (localUltra_allProductsDefined_iff U G L _ 200).2
    (hA.mono fun _ hi => hi.approximate.allProducts)
  refine M.zero_escape_normal_window_nss hD hR hB1 hBi
    (hdom.mono M (Set.Subset.refl _) (by omega : 6 ≤ 200))
    (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)) ?_ 1000 ?_
  · intro x _ y _ z hm
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      strong_localUltra_product U G L A hd hr hA ((LocalGroupAlgebra.Product.pair_iff M _ _ _).2 hm)
  · have htrap := localUltra_power_trapping U G L (fun i => (A i : Set (G i)))
      (fun i => (L i).wordPower (A i : Set (G i)) 100) 1000
      (hA.mono fun _ hi => by obtain ⟨S,_,_,_,hf,_⟩ := hi.trapping; exact hf)
    intro x hx
    apply htrap x
    intro j hj hj'
    obtain ⟨y,hy,hp⟩ := hx j hj hj'
    have hy100 : y ∈ M.wordPower B 100 :=
      M.wordPower_subset_wordPower hB1 hdom (by omega : 3 ≤ 100) (by omega) hy
    refine ⟨y,?_,hp⟩
    simpa only [M,B,localUltra_wordPower] using hy100
end DirectedCycles
