import DirectedCycles.StrongLocalCentralSegment
import DirectedCycles.StrongLocalSelectedCentralSet
import DirectedCycles.LocalConnectedScaledModel
import DirectedCycles.LocalModelEscapeNeighbourhood
import DirectedCycles.LocalScaledCentrality
import DirectedCycles.LocalProductDomainTransfer

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- Actual strong finite local NSS data and a connected local model produce
one specified proper central progression family whose image is the compact
unit segment of a nontrivial central continuous one-parameter map. The scale,
centralizing neighbourhood and image equality are all derived. -/
theorem strong_local_connected_central_curve (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ (ι : Type*) (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
        (L : ∀ i, LocalGroupAlgebra (G i))
        (_hd : ∀ i, (L i).DivisionClosed) (_hr : ∀ i, (L i).Reversible)
        (A : ∀ i, Finset (G i)),
        (∀ i, IsStrongLocalFiniteApproximateGroup (L i) K (A i)) →
        (∀ i, (L i).IsNSS (A i : Set (G i))) →
        (∀ i, ∃ g ∈ A i, g ≠ (L i).one) →
        ∀ (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
          [T2Space H] [PreconnectedSpace H] [Nontrivial H]
          (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
          (V : Set H), IsCompact V →
          (∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1) →
          (∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V) →
          ∀ W : Set H, IsOpen W → (1 : H) ∈ W →
          (∀ z, π.toFun z ∈ W → z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) →
          (∀ y ∈ W, ∃ z, π.toFun z = y) →
          ∃ (N : ι → ℕ) (P : ∀ i, Finset (G i)) (φ : ℝ → H),
            (∀ i, 2 ≤ N i ∧ (P i).card = 2*N i-1 ∧ (P i : Set (G i)) ⊆ A i ∧
              (L i).CentralLocalSet (P i : Set (G i))
                {x | (L i).escapeNorm (A i) x < 1/1001} {x | (L i).escapeNorm (A i) x < δ}) ∧
            (∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i) ∧
            Continuous φ ∧ φ 0 = 1 ∧ (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧ φ 1 ≠ 1 ∧
            (∀ t : ℝ, ∀ y : H, Commute (φ t) y) ∧
            π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) =
              φ '' Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨δ,hδ,hδhalf,hseg⟩ := strong_local_central_segment K
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro ι U G _ L hd hr A hA hNSS hne H _ _ _ _ _ _ π V hV hVNSS himage W hWo hW1 hsmall hthick
  choose u hu hu1 N hN p hprev hexit hnorm hmin hcent hmem using
    fun i => hseg (G i) (L i) (A i) (hA i) (hd i) (hr i) (hNSS i) (hne i)
  let B : ∀ i, Set (G i) := fun i => (A i : Set (G i))
  let J := localUltraAlgebra (U : Filter ι) G L
  have hB1 : J.one ∈ localUltraSet (U : Filter ι) G B :=
    (localUltraMk_mem_iff (U : Filter ι) G B _).2 (Filter.Eventually.of_forall fun i => (hA i).approximate.one_mem)
  have hBdom : J.AllProductsDefined (localUltraSet (U : Filter ι) G B) 2 :=
    (localUltra_allProductsDefined_iff U G L B 2).2 (Filter.Eventually.of_forall fun i =>
      (hA i).approximate.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 2 ≤ 200))
  have hbin : ∀ x ∈ localUltraSet (U : Filter ι) G B, ∀ y ∈ localUltraSet (U : Filter ι) G B,
      J.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hBdom [x,y] (by simp) (by aesop)
    exact ⟨z,(LocalGroupAlgebra.Product.pair_iff J x y z).1 hz⟩
  have hsegments := fun k => exists_local_long_power_segment_of_connected_model J
    (localUltraSet (U : Filter ι) G B) hB1 hbin π W hWo hW1 hsmall hthick k
  have hNpos : ∀ᶠ i in (U : Filter ι), 0 < N i := Filter.Eventually.of_forall fun i => by have := hN i; omega
  have hunbounded := local_minimal_first_escape_unbounded U G L B u N hNpos
    (Filter.Eventually.of_forall hnorm) (Filter.Eventually.of_forall hmin) hsegments
  have hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ 2*N i := Filter.Eventually.of_forall fun _ => le_rfl
  have hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ B i, (L i).inv x ∈ B i :=
    Filter.Eventually.of_forall fun i => (hA i).approximate.inv_mem
  obtain ⟨φ,hφcont,hφ0,hφadd,hφ1,hformula⟩ := exists_local_scaled_one_parameter U G L hd hr B u N
    (fun i => 2*N i) p hunbounded hM hi (Filter.Eventually.of_forall hprev)
    (Filter.Eventually.of_forall hexit) π V hV hVNSS himage W hW1 hsmall
  choose P hPeq hPcard hPA hPlocal using fun i => strong_local_central_set_of_segment (L i)
    (hA i) (hd i) (hr i) (hNSS i) (hu i) (hu1 i) (hN i) (p i) (hprev i) (hexit i) hδhalf (hcent i)
  refine ⟨N,P,φ,fun i => ⟨hN i,hPcard i,hPA i,hPlocal i⟩,hunbounded,hφcont,hφ0,hφadd,hφ1,?_,?_⟩
  · obtain ⟨O,hOo,hO1,hOW,hOsmall⟩ := local_model_internal_escape_neighbourhood U G L B hB1 hbin
      π W hWo hW1 hsmall hδ
    let C : ∀ i, Set (G i) := fun i => {x | (L i).escapeNorm (B i) x < δ}
    have hc : ∀ᶠ i in (U : Filter ι), ∀ x ∈ C i, x ∈ B i ∧ (L i).Commute x (u i) := by
      apply Filter.Eventually.of_forall
      intro i x hx
      change (L i).escapeNorm (B i) x < δ at hx
      exact ⟨(L i).mem_of_escapeNorm_lt_one (hA i).approximate.one_mem (by linarith),hcent i x hx⟩
    apply local_scaled_curve_central U G L hd B C u N (fun i => 2*N i) p
      ((hunbounded 2).mono fun i hni => ⟨by omega,by omega⟩) (Filter.Eventually.of_forall hu) hi
      (Filter.Eventually.of_forall fun i => (hA i).approximate.allProducts.mono (L i) (Set.Subset.refl _) (by omega : 3 ≤ 200))
      (Filter.Eventually.of_forall hprev) hc π φ hφ0 hφadd hformula O (hOo.mem_nhds hO1)
    intro y hy
    obtain ⟨z,hz⟩ := hthick y (hOW hy)
    exact ⟨z,hOsmall z (hz.symm ▸ hy),hz⟩
  · have he : (fun i => (P i : Set (G i))) = (fun i => (p i).shortSignedSet (N i)) := funext hPeq
    rw [he]
    exact local_shortProgression_model_image_eq U G L hd hr B u N (fun i => 2*N i) p hunbounded hM hi
      (Filter.Eventually.of_forall hprev) π V hVNSS himage φ hformula
end DirectedCycles
