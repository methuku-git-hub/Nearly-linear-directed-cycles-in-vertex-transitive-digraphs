import DirectedCycles.LocalLieTargetPrescribedCentralQuotient
import DirectedCycles.LocalToLocalCentralQuotientLocalSandwich
import DirectedCycles.LocalToLocalComponentProjectedEscapeKernel
import DirectedCycles.LocalToLocalModelEscapeControl

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles
variable {ι H E : Type*} [TopologicalSpace H] [T2Space H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E H] {M : LocalGroupAlgebra H} (X : LocalExponentialData (E := E) M)

/-- The prescribed exponential source windows carry the actual descended
central model, its exact kernel, its compact NSS image and internal compact/
open approximation. All windows and finite quotients are constructed together. -/
theorem local_lie_target_prescribed_central_model
    (hM : LocalGroupSmoothness (E := E) M)
    (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Fintype (G i)]
    (L : ∀ i, LocalGroupAlgebra (G i)) (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Finset (G i)) {Ka : ℕ} (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    (V : Set H) (hV : IsCompact V) (htrap : ∀ O : Set H, O ∈ 𝓝 M.one → ∃ N : ℕ, 1 ≤ N ∧
      ∀ x : H, (∀ n ≤ N, M.PowerIn V x n) → x ∈ O)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    (U₀ : Set H) (hU₀ : IsOpen U₀) (hU₀1 : M.one ∈ U₀)
    (hsmall : π.toFun ⁻¹' U₀ ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hsandwich : ∀ F O : Set H, IsCompact F → IsOpen O → F ⊆ O → O ⊆ U₀ →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' O)
    (P : ∀ i, Finset (G i)) {τ : ℝ} (hτ : 0 < τ)
    (hP : ∀ i, (L i).CentralLocalSet (P i : Set (G i)) {x | (L i).escapeNorm (A i) x < 1/1001}
      {x | (L i).escapeNorm (A i) x < τ})
    {Q : Set H} (T : M.CentralQuotientData Q) (hWo : IsOpen T.small)
    [T2Space T.Carrier]
    (hPeq : π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))) = Q)
    (Vq : Set T.Carrier)
    (Z : Set H) (hZ : IsCompact Z) (hZ1 : M.one ∈ interior Z) (hZW : Z ⊆ T.small) (hZU₀ : Z ⊆ U₀)
    (hZVq : ∀ x : T.small, x.val ∈ Z → T.project x ∈ Vq) :
    ∃ K : ℕ, ∃ R : ℝ, 1 ≤ K ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ B : ∀ i, Finset (G i), ∃ D : ∀ i, (L i).CentralQuotientData (P i : Set (G i)),
      ∃ J : ℕ, 1 ≤ J ∧
        π.toFun ⁻¹' (X.chart '' Metric.closedBall (0 : E) r) ⊆
          localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆
          π.toFun ⁻¹' (X.chart '' Metric.ball (0 : E) ((1001/1000 : ℝ)*r)) ∧
        (∀ i, IsLocalFiniteApproximateGroup (L i) K (B i) ∧ B i ⊆ A i ∧
          (D i).small = (L i).wordPower (B i : Set (G i)) 200 ∧
          (∀ n ≤ 200, (L i).wordPower (B i : Set (G i)) n ⊆ (D i).small) ∧
          (D i).small ⊆ {x | (L i).escapeNorm (A i) x < τ} ∧
          IsLocalFiniteApproximateGroup (D i).algebra K ((D i).finiteImage (B i)) ∧
          (D i).algebra.DivisionClosed ∧ (D i).algebra.Reversible) ∧
        (∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (B i)) ∧
        (∀ᶠ i in (U : Filter ι), (A i).card ≤ J*((D i).finiteImage (B i)).card*(P i).card) ∧
        ∃ Ψ : LocalGroupHom
          (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra))
          T.algebra,
          (∃ hDW : ∀ x ∈ (LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L
              (fun i => (P i : Set (G i))) D).small, π.toFun x ∈ T.small,
            ∀ hPQ : ∀ p ∈ localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))), π.toFun p ∈ Q,
            Ψ = ((LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).localModelQuotientHom
              T π hPQ hDW).comp (LocalGroupAlgebra.CentralQuotientData.quotientUltraHom
                U G L (fun i => (P i : Set (G i))) D hd hr)) ∧
          (∀ a : ∀ i, (D i).small,
            Ψ.toFun (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i))) =
              T.algebra.one →
            π.toFun (localUltraMk (U : Filter ι) G (fun i => (a i).val)) ∈
              π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i)))) ∧
          (∀ z, Ψ.toFun z ∈ Vq) ∧
          ∀ F O : Set T.Carrier, IsCompact F → IsOpen O → F ⊆ O →
            ∃ S : ∀ i, Finset (D i).Carrier,
              Ψ.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ∧
              localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (S i : Set (D i).Carrier)) ⊆ Ψ.toFun ⁻¹' O := by
  obtain ⟨ε,hε,hcontrol⟩ := local_to_local_model_escape_sublevel_small U G L M (fun i => (A i : Set (G i)))
    (Filter.Eventually.of_forall fun i => (hA i).one_mem) π V htrap himage (interior Z) (isOpen_interior.mem_nhds hZ1)
  have hP' : ∀ i, (L i).CentralLocalSet (P i : Set (G i)) {x | (L i).escapeNorm (A i) x < 1/1001}
      {x | (L i).escapeNorm (A i) x < min τ ε} := by
    intro i
    refine ⟨(hP i).one_mem,(hP i).inv_mem,(hP i).mul_mem,?_⟩
    intro p hp x hx
    exact (hP i).central p hp x ((show (L i).escapeNorm (A i) x < min τ ε from hx).trans_le (min_le_left _ _))
  obtain ⟨K,R,hK,hR,hwin⟩ := local_lie_target_prescribed_central_quotient_windows X hM U G L hd hr A hA π V hV
    (by rintro _ ⟨x,hx,rfl⟩; exact himage x hx) U₀ (hU₀.mem_nhds hU₀1) hsmall hsandwich P (lt_min hτ hε) hP'
  refine ⟨K,R,hK,hR,?_⟩
  intro r hr0 hrR
  obtain ⟨B,D,J,hJ,hBin,hBout,hB,hstrong,hcard⟩ := hwin r hr0 hrR
  let E' := LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D
  have hEZ : ∀ x ∈ E'.small, π.toFun x ∈ Z := by
    intro x hx
    apply interior_subset
    apply hcontrol x
    apply (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).2
      (Filter.Eventually.of_forall fun i y hy =>
        (show (L i).escapeNorm (A i) y < min τ ε from (hB i).2.2.2.2.1 hy).trans_le (min_le_right _ _)) hx
  have hDW : ∀ x ∈ E'.small, π.toFun x ∈ T.small := fun x hx => hZW (hEZ x hx)
  have hPQ : ∀ p ∈ localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))), π.toFun p ∈ Q := by
    intro p hp
    rw [← hPeq]
    exact ⟨p,hp,rfl⟩
  let F := E'.localModelQuotientHom T π hPQ hDW
  let Ψ := F.comp (LocalGroupAlgebra.CentralQuotientData.quotientUltraHom U G L (fun i => (P i : Set (G i))) D hd hr)
  have hkernel := LocalGroupAlgebra.CentralQuotientData.local_to_local_component_kernel_of_quotient_kernel U G L
    (fun i => (P i : Set (G i))) D hd hr M T.algebra π F
    (π.toFun '' localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i)))) (by
      intro a ha
      rw [hPeq]
      exact (E'.localModelQuotientHom_kernel T π hPQ hDW a).1 ha)
  have hFimage : ∀ y : E'.Carrier, F.toFun y ∈ Vq := by
    intro y
    induction y using Quotient.inductionOn with
    | h a =>
      rw [show F = E'.localModelQuotientHom T π hPQ hDW from rfl,
        E'.localModelQuotientHom_projection]
      exact hZVq _ (hEZ a.val a.property)
  let Cw : Set T.small := Subtype.val ⁻¹' Z
  have hCw : IsCompact Cw := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hZ
    (by simpa only [Subtype.range_coe] using hZW)
  have hCwU : Subtype.val '' Cw ⊆ U₀ := by
    rintro _ ⟨x,hx,rfl⟩
    exact hZU₀ hx
  have hsw := LocalGroupAlgebra.CentralQuotientData.localModelQuotientHom_local_internal_sandwich U G L
    (fun i => (P i : Set (G i))) D hd hr T hWo π hPQ hDW Cw hCw
    (fun x => hEZ x.val x.property) U₀ hU₀ hCwU hsandwich
  refine ⟨B,D,J,hJ,hBin,hBout,?_,hstrong,hcard,Ψ,⟨hDW,fun _ => rfl⟩,hkernel,fun z => hFimage ((LocalGroupAlgebra.CentralQuotientData.quotientUltraHom U G L (fun i => (P i : Set (G i))) D hd hr).toFun z),hsw⟩
  intro i
  exact ⟨(hB i).1,(hB i).2.1,(hB i).2.2.1,(hB i).2.2.2.1,
    fun x hx => (show (L i).escapeNorm (A i) x < min τ ε from (hB i).2.2.2.2.1 hx).trans_le (min_le_left _ _),
    (hB i).2.2.2.2.2⟩
end DirectedCycles
