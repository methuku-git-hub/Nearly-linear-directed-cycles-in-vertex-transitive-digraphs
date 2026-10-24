import DirectedCycles.LocalPowerSegmentRestriction
import DirectedCycles.LocalNegligibleEscapePower
import DirectedCycles.LocalCentralQuotientUltraHom

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))

/-- The actual descended quotient model sends an endpoint to the identity
when quotient escape times its source scale is infinitesimal. The proved
quotient-ultraproduct equivalence then places its original model image in the
specified kernel set. No source quotient NSS property is assumed. -/
theorem projected_negligible_escape_kernel
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (B : ∀ i, Finset (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (N i))
    (hu : ∀ i, u i ∈ (D i).small)
    (hp : ∀ i, ∀ n ≤ N i, (p i).power n ∈ (D i).small)
    (hB1 : ∀ᶠ i in (U : Filter ι), (D i).algebra.one ∈ (D i).finiteImage (B i))
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      (D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier)
        ((D i).project ⟨u i,hu i⟩)*(N i : ℝ) < ε)
    {H T : Type*} [Group H] (M : LocalGroupAlgebra T)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (F : LocalGroupHom (ultraproduct U G L P D).algebra M) (Q : Set H)
    (hkernel : ∀ a : (ultraproduct U G L P D).small,
      F.toFun ((ultraproduct U G L P D).project a) = M.one → π.toFun a.val ∈ Q)
    (V : Set T)
    (hNSS : ∀ x : T, ∀ q : M.PowerSequence x, (∀ n, q.power n ∈ V) → x = M.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
        (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)),
      F.toFun ((quotientUltraHom U G L P D hd hr).toFun z) ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).power (N i))) ∈ Q := by
  let q := fun i => (D i).projectPowerSegment (p i) (hu i) (hp i)
  let Ψ := F.comp (quotientUltraHom U G L P D hd hr)
  have he := local_model_kills_negligible_escape_power U (fun i => (D i).Carrier)
    (fun i => (D i).algebra) M (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier))
    (fun i => (D i).project ⟨u i,hu i⟩) N q hB1 hN hsmall Ψ V hNSS himage
  let a : ∀ i, (D i).small := fun i => ⟨(p i).power (N i),hp i (N i) le_rfl⟩
  have hrepr : localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (q i).power (N i)) =
      componentProjection U G L P D (localUltraMk (U : Filter ι) (fun i => (D i).small) a) := by
    apply Quotient.sound
    exact Filter.Eventually.of_forall fun i => (D i).projectPowerSegment_value (p i) (hu i) (hp i) le_rfl
  change F.toFun (quotientUltraEquiv U G L P D
    (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (q i).power (N i)))) = M.one at he
  rw [hrepr,quotientUltraEquiv_projection] at he
  have hk := hkernel (localUltraWindowMap (U : Filter ι) G (fun i => (D i).small)
    (localUltraMk (U : Filter ι) (fun i => (D i).small) a)) he
  exact hk
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
