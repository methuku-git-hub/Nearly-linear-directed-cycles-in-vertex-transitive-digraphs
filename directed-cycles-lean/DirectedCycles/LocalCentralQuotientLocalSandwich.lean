import DirectedCycles.LocalInternalWindowCompactSandwich
import DirectedCycles.LocalInternalQuotientSandwich
import DirectedCycles.LocalCentralModelQuotientMap
import DirectedCycles.LocalCentralQuotientUltraHom
import DirectedCycles.LocalQuotientTopology

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
variable {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]
    {Q V W : Set H} (hQ : LocalNormalSet Q V)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V) (hWo : IsOpen W)
    [T2Space (hQ.WindowQuotient hW1 hWi hW6)]
local notation "Du" => ultraproduct U G L P D

include hWo in
/-- The actual component central-quotient model inherits the finite internal
compact/open sandwich from approximation on a local model neighbourhood.
The proof uses its constructed projection formula,
compact control inside the target window, and actual finite component images. -/
theorem modelQuotientHom_local_internal_sandwich
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (hPQ : ∀ p ∈ localUltraSet (U : Filter ι) G P, π.toFun p ∈ Q)
    (hDW : ∀ x ∈ (Du).small, π.toFun x ∈ W)
    (C : Set W) (hC : IsCompact C)
    (hπC : ∀ x : (Du).small, (⟨π.toFun x.val,hDW x.val x.property⟩ : W) ∈ C)
    (U₀ : Set H) (hU₀ : IsOpen U₀) (hCU₀ : Subtype.val '' C ⊆ U₀)
    (hsandwich : ∀ F O : Set H, IsCompact F → IsOpen O → F ⊆ O → O ⊆ U₀ →
      ∃ B : ∀ i, Finset (G i),
        π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' O) :
    let Ψ := ((Du).modelQuotientHom hQ hW1 hWi hW6 π hPQ hDW).comp (quotientUltraHom U G L P D hd hr)
    ∀ F O : Set (hQ.WindowQuotient hW1 hWi hW6), IsCompact F → IsOpen O → F ⊆ O →
      ∃ B : ∀ i, Finset (D i).Carrier,
        Ψ.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (B i : Set (D i).Carrier)) ∧
        localUltraSet (U : Filter ι) (fun i => (D i).Carrier) (fun i => (B i : Set (D i).Carrier)) ⊆ Ψ.toFun ⁻¹' O := by
  classical
  intro Ψ
  let π' : LocalUltraproduct (U : Filter ι) (fun i => (D i).small) → W := fun x =>
    ⟨π.toFun (localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) x).val,
      hDW _ (localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) x).property⟩
  have hcomm : ∀ x, (π' x).val = π.toFun
      (localUltraMap (U : Filter ι) (fun i => (D i).small) G (fun _ => Subtype.val) x) := by
    intro x
    induction x using Quotient.inductionOn with
    | h a => rfl
  have hsource := local_internal_window_sandwich_of_compact_range U G (fun i => (D i).small) W hWo
    π.toFun π' hcomm (Subtype.val '' C) U₀ (hC.image continuous_subtype_val) hU₀ hCU₀
    (fun x => ⟨π' x,hπC (localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) x),rfl⟩) hsandwich
  apply local_internal_quotient_sandwich U (fun i => (D i).small) (fun i => (D i).Carrier)
    (fun i => ⟨(L i).one,(D i).one_mem⟩) (fun i => (D i).project)
    (fun _ => Quotient.mk_surjective) π' Ψ.toFun (hQ.windowMk hW1 hWi hW6)
    (hQ.continuous_windowMk hW1 hWi hW6) _ C hC
    (fun x => hπC (localUltraWindowMap (U : Filter ι) G (fun i => (D i).small) x)) hsource
  intro x
  change ((Du).modelQuotientHom hQ hW1 hWi hW6 π hPQ hDW).toFun
    (quotientUltraEquiv U G L P D (componentProjection U G L P D x)) = _
  rw [quotientUltraEquiv_projection]
  rfl
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
