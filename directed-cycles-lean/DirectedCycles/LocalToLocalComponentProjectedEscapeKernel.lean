module

public import DirectedCycles.LocalProjectedEscapeKernel

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))

/-- Component form of the projected kernel deduction, convenient for exact
restriction of the index set. The model is an actual partial homomorphism. -/
theorem local_to_local_component_projected_negligible_escape_kernel
    (B : ∀ i, Finset (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (N i))
    (hu : ∀ i, u i ∈ (D i).small)
    (hp : ∀ i, ∀ n ≤ N i, (p i).power n ∈ (D i).small)
    (hB1 : ∀ᶠ i in (U : Filter ι), (D i).algebra.one ∈ (D i).finiteImage (B i))
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      (D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier)
        ((D i).project ⟨u i,hu i⟩)*(N i : ℝ) < ε)
    {H T : Type*} (R : LocalGroupAlgebra H) (M : LocalGroupAlgebra T)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) R)
    (Ψ : LocalGroupHom (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra)) M)
    (Q : Set H)
    (hkernel : ∀ a : ∀ i, (D i).small,
      Ψ.toFun (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i))) = M.one →
        π.toFun (localUltraMk (U : Filter ι) G (fun i => (a i).val)) ∈ Q)
    (V : Set T)
    (hNSS : ∀ x : T, ∀ q : M.PowerSequence x, (∀ n, q.power n ∈ V) → x = M.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
        (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)), Ψ.toFun z ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).power (N i))) ∈ Q := by
  let q := fun i => (D i).projectPowerSegment (p i) (hu i) (hp i)
  have he := local_model_kills_negligible_escape_power U (fun i => (D i).Carrier)
    (fun i => (D i).algebra) M (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier))
    (fun i => (D i).project ⟨u i,hu i⟩) N q hB1 hN hsmall Ψ V hNSS himage
  apply hkernel (fun i => ⟨(p i).power (N i),hp i (N i) le_rfl⟩)
  convert he using 1
  congr 1
  apply Quotient.sound
  exact Filter.Eventually.of_forall fun i =>
    ((D i).projectPowerSegment_value (p i) (hu i) (hp i) le_rfl).symm

/-- The actual quotient-ultraproduct homomorphism supplies the component
kernel condition. This is an equality of the constructed projections. -/
theorem local_to_local_component_kernel_of_quotient_kernel
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    {H T : Type*} (R : LocalGroupAlgebra H) (M : LocalGroupAlgebra T)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) R)
    (F : LocalGroupHom (ultraproduct U G L P D).algebra M) (Q : Set H)
    (hkernel : ∀ a : (ultraproduct U G L P D).small,
      F.toFun ((ultraproduct U G L P D).project a) = M.one → π.toFun a.val ∈ Q) :
    ∀ a : ∀ i, (D i).small,
      (F.comp (quotientUltraHom U G L P D hd hr)).toFun
        (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i))) = M.one →
      π.toFun (localUltraMk (U : Filter ι) G (fun i => (a i).val)) ∈ Q := by
  intro a ha
  change F.toFun (quotientUltraEquiv U G L P D (componentProjection U G L P D
    (localUltraMk (U : Filter ι) (fun i => (D i).small) a))) = M.one at ha
  rw [quotientUltraEquiv_projection] at ha
  exact hkernel _ ha
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
