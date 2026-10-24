import DirectedCycles.LocalNestedFirstExitGeometry
import DirectedCycles.LocalFirstExitOrder
import DirectedCycles.LocalCentralCorrectionContradiction
import DirectedCycles.LieCentralCurveAlignment
import DirectedCycles.LocalNestedEscapeRatio

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
variable {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E H]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ H]

include hLie in
/-- The complete geometric contradiction for a least quotient lift. Both
nested scale comparisons, the signed central direction, the compatible inner
central curve, all correction domains and progression membership are derived.
The preceding quotient-model argument must supply unbounded inner exit time
and centrality of the actual first-exit endpoint. -/
theorem local_least_lift_geometric_contradiction
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {Ka Kb : ℕ} (A B : ∀ i, Finset (G i))
    (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (hB : ∀ i, IsLocalFiniteApproximateGroup (L i) Kb (B i))
    (hBA : ∀ i, (B i : Set (G i)) ⊆ A i)
    (u g : ∀ i, G i) (Nu Ng Ku Kg : ι → ℕ)
    (pu : ∀ i, (L i).PowerSegment (u i) (2*Nu i))
    (pg : ∀ i, (L i).PowerSegment (g i) (2*Ng i))
    (qu : ∀ i, (L i).PowerSegment (u i) (4*Ku i))
    (qg : ∀ i, (L i).PowerSegment (g i) (4*Kg i))
    (hpos : ∀ i, 2 ≤ Nu i ∧ 2 ≤ Ng i ∧ 2 ≤ Ku i ∧ 2 ≤ Kg i)
    (hup : ∀ i, ∀ n < Nu i, (pu i).power n ∈ A i)
    (hgp : ∀ i, ∀ n < Ng i, (pg i).power n ∈ A i)
    (huq : ∀ i, ∀ n < Ku i, (qu i).power n ∈ B i)
    (hgq : ∀ i, ∀ n < Kg i, (qg i).power n ∈ B i)
    (hue : ∀ i, (pu i).power (Nu i) ∉ A i)
    (hge : ∀ i, (pg i).power (Ng i) ∉ A i)
    (hue' : ∀ i, (qu i).power (Ku i) ∉ B i)
    (hge' : ∀ i, (qg i).power (Kg i) ∉ B i)
    (huq8 : ∀ i, ∀ n ≤ 4*Ku i, (qu i).power n ∈ (L i).wordPower (B i : Set (G i)) 8)
    (hgq8 : ∀ i, ∀ n ≤ 4*Kg i, (qg i).power n ∈ (L i).wordPower (B i : Set (G i)) 8)
    (hu : ∀ i, u i ∈ B i) (hg : ∀ i, g i ∈ B i)
    (hminouter : ∀ i, 1/(Nu i : ℝ) ≤ 1/(Ng i : ℝ))
    (hNu : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < Nu i)
    (hKg : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < Kg i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V) (hVNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    {R r δ : ℝ} (hr0 : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : (1001/1000)*r < R)
    (hinj : Set.InjOn (lieExponential (G := H) (E := E)) (Metric.ball 0 R))
    (hAo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*r))
    (hAs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) r →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hBo : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))),
      π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.closedBall (0 : E) ((1001/1000)*δ*r))
    (hBs : ∀ z, π.toFun z ∈ (lieExponential (G := H) (E := E)) '' Metric.ball (0 : E) (δ*r) →
      z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (φ : ℝ → H) (hφ0 : φ 0 = 1) (hφc : ContinuousAt φ 0)
    (hφadd : ∀ s t : ℝ, φ (s+t) = φ s*φ t)
    (hφform : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u Nu (fun i => 2*Nu i) pu t))
    (hendpoint : π.toFun (localUltraMk (U : Filter ι) G (fun i => (qg i).power (Kg i))) ∈
      φ '' Set.Icc (-1 : ℝ) 1)
    (P : ∀ i, Set (G i)) (hPeq : ∀ i, P i = (pu i).shortSignedSet (Nu i))
    (D : ∀ i, (L i).CentralQuotientData (P i))
    (hBsmall : ∀ i, (B i : Set (G i)) ⊆ (D i).small)
    (hmin : ∀ i, ∀ z : (D i).small, z.val ∈ B i →
      (D i).project z = (D i).project ⟨g i,hBsmall i (hg i)⟩ →
        (L i).escapeNorm (B i : Set (G i)) (g i) ≤ (L i).escapeNorm (B i : Set (G i)) z.val)
    (hnorm : ∀ i, (L i).escapeNorm (B i : Set (G i)) (g i) = 1/(Kg i : ℝ))
    (hgu : ∀ i, (L i).Commute (g i) (u i)) : False := by
  have hsub : localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆
      localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) :=
    (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).2 (Filter.Eventually.of_forall hBA)
  have hAi := Filter.Eventually.of_forall (f := (U : Filter ι)) fun i => (hA i).inv_mem
  have hBi := Filter.Eventually.of_forall (f := (U : Filter ι)) fun i => (hB i).inv_mem
  have hKuNu : ∀ i, Ku i ≤ Nu i := fun i => (L i).first_exit_mono (hBA i) (pu i) (qu i)
    (by omega) (by omega) (huq i) (hue i)
  have hKgNg : ∀ i, Kg i ≤ Ng i := fun i => (L i).first_exit_mono (hBA i) (pg i) (qg i)
    (by omega) (by omega) (hgq i) (hge i)
  have hNg : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < Ng i :=
    fun n => (hKg n).mono fun i hi => hi.trans_le (hKgNg i)
  obtain ⟨X,hXder,_,_,_⟩ := lieGroup_one_parameter_coordinate_derivative (E := E) φ hφ0 hφc hφadd
  have hXnorm := local_first_exit_tangent_annulus U G L hd hr (fun i => (A i : Set (G i))) u Nu
    (fun i => 2*Nu i) pu hNu (Filter.Eventually.of_forall fun _ => le_rfl) hAi
    (Filter.Eventually.of_forall hup) (Filter.Eventually.of_forall hue) π V hVNSS himage φ hφ0 hφc hφadd
    hφform hXder (by positivity) hR hinj hAo hAs
  obtain ⟨ψ,t',hψc,hψ0,hψadd,hψform,ht'lo,ht'hi,hψexp,_,hKu,hratiou⟩ :=
    local_nested_first_exit_geometry U G L hd hr (fun i => (A i : Set (G i))) (fun i => (B i : Set (G i)))
      u Nu (fun i => 2*Nu i) Ku (fun i => 4*Ku i) pu qu (Filter.Eventually.of_forall hBA) hNu
      (Filter.Eventually.of_forall fun _ => le_rfl) (Filter.Eventually.of_forall fun i => by omega)
      hAi hBi (Filter.Eventually.of_forall hup) (Filter.Eventually.of_forall huq)
      (Filter.Eventually.of_forall hue) (Filter.Eventually.of_forall hue') π V hV hVNSS himage
      hr0 hδ hδ1 hR hinj hAo hAs hBo hBs φ hφ0 hφc hφadd hφform hXder
  obtain ⟨_,_,_,hratiog⟩ := local_nested_escape_ratio U G L hd hr
    (fun i => (A i : Set (G i))) (fun i => (B i : Set (G i))) g Ng (fun i => 2*Ng i) Kg (fun i => 4*Kg i)
    pg qg (Filter.Eventually.of_forall hBA) hNg (Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall fun i => by omega) hAi hBi (Filter.Eventually.of_forall hgp)
    (Filter.Eventually.of_forall hgq) (Filter.Eventually.of_forall hge) (Filter.Eventually.of_forall hge')
    π V hV hVNSS himage hr0 hδ hδ1 hR hinj hAo hAs hBo hBs
  have hratio := local_nested_minimal_exit_comparison U Nu Ng Ku Kg hδ
    (Filter.Eventually.of_forall fun i => by have := hpos i; omega)
    (Filter.Eventually.of_forall hminouter) (hratiou.mono fun _ hi => hi.1) (hratiog.mono fun _ hi => hi.2)
  have hsmallR : (1001/1000)*δ*r < R := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0 ≤ (1001/1000)*r by positivity)
    nlinarith
  obtain ⟨χ,v,hχc,hχ0,hχadd,_,hχv,hχform,hχnorm,_⟩ := local_lie_first_exit_curve U G L hd hr
    (fun i => (B i : Set (G i))) g Kg (fun i => 4*Kg i) qg hKg
    (Filter.Eventually.of_forall fun i => by omega) hBi (Filter.Eventually.of_forall hgq)
    (Filter.Eventually.of_forall hge') π V hV hVNSS (fun z hz => himage z (hsub hz))
    (mul_pos hδ hr0) (by positivity) hsmallR hinj hBo hBs
  have hχend : χ 1 ∈ φ '' Set.Icc (-1 : ℝ) 1 := by
    rw [hχform 1 (by norm_num),localScaledPower_one]
    exact hendpoint
  obtain ⟨t,_,hthi,_,hχφ⟩ := lie_central_curve_alignment hr0 hδ hδ1 hR hinj φ χ hφ0 hχ0
    hφc hχc.continuousAt hφadd hχadd hXder hχv hXnorm hχnorm hχend
  have hφexp := lie_one_parameter_eq_exponential φ hφ0 hφc hφadd hXder
  let C := fun i => (L i).wordPower (A i : Set (G i)) 8
  have hB8A8 : ∀ i, (L i).wordPower (B i : Set (G i)) 8 ⊆ C i := by
    intro i x hx
    obtain ⟨l,hl,hm,hp⟩ := hx
    exact ⟨l,hl,fun a ha => hBA i (hm a ha),hp⟩
  have huC : ∀ i, u i ∈ C i := by
    intro i
    apply (L i).wordPower_subset_wordPower (hA i).one_mem (hA i).allProducts (by omega : 1 ≤ 8) (by omega)
    rw [(L i).wordPower_one]
    exact hBA i (hu i)
  have hP : ∀ i, ∀ k : ℤ, k.natAbs < Ku i → (qu i).signedPower k ∈ P i := by
    intro i k hk
    rw [hPeq i]
    have hkN : k.natAbs < Nu i := hk.trans_le (hKuNu i)
    have he := ((qu i).product k.natAbs (by omega)).unique (L i)
      ((pu i).product k.natAbs (by omega))
    refine ⟨k,hkN,?_⟩
    dsimp only [LocalGroupAlgebra.PowerSegment.signedPower]
    split_ifs <;> simp only [he]
  exact local_central_correction_contradiction U G L hd hr B g u Kg (fun i => 4*Kg i) Ku (fun i => 4*Ku i)
    qg qu hKg hKu (fun i => by omega) (fun _ => le_rfl) hBi (Filter.Eventually.of_forall hgq)
    (Filter.Eventually.of_forall huq) π V hVNSS (fun z hz => himage z (hsub hz)) χ ψ hχform hψform hψadd
    hr0 hδ X hXnorm.2 (fun s => (hχφ s).trans (hφexp (t*s))) hψexp
    (by nlinarith) (by linarith) (by linarith) (hratio.mono fun _ hi => hi.le) hBs
    (fun i => by have := hpos i; omega) (fun i => by have := hpos i; omega) C P D hBsmall hg hmin hnorm
    (fun i _ hx => (L i).inv_mem_wordPower (hr i) (hA i).inv_mem hx)
    (fun i => (hA i).allProducts.wordPower (L i) (by omega : 8*4 ≤ 200)) huC
    (fun i n hn => hB8A8 i (hgq8 i n (by omega)))
    (fun i n hn => hB8A8 i (huq8 i n (by omega))) hgu hP
end DirectedCycles
