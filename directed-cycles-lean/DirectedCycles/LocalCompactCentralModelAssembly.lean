import DirectedCycles.LocalFiniteSelectedCentralQuotient
import Mathlib.Topology.Compactness.LocallyCompact
import DirectedCycles.LocalCentralQuotientUltraData
import DirectedCycles.LocalCentralModelQuotientMap
import DirectedCycles.LocalModelEscapeControl

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles

/-- Central quotient windows are chosen with compact model-image control
strictly inside the target window. This supplies the compactness required for
internal good-model descent and retains the source escape-sublevel bound. -/
theorem local_compact_central_quotient_model_assembly {ι : Type*} (U : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Fintype (G i)] (L : ∀ i, LocalGroupAlgebra (G i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A P : ∀ i, Finset (G i)) {K : ℕ} (hK : 1 ≤ K)
    (hA : ∀ i, IsStrongLocalFiniteApproximateGroup (L i) K (A i))
    {r : ℝ} (hr0 : 0 < r)
    (hP : ∀ i, (L i).CentralLocalSet (P i : Set (G i))
      {x | (L i).escapeNorm (A i) x < 1/1001} {x | (L i).escapeNorm (A i) x < r})
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V)
    (hNSS : ∀ y : H, (∀ n : ℕ, y^n ∈ V) → y = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), π.toFun z ∈ V)
    {Q T W : Set H} (hQ : LocalNormalSet Q T)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ T) (hWo : IsOpen W)
    (hPQ : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (P i : Set (G i))), π.toFun z ∈ Q) :
    ∃ (J : ℕ) (η : ℝ), 1 ≤ J ∧ 0 < η ∧
      ∃ D : ∀ i, (L i).CentralQuotientData (P i : Set (G i)), ∃ B : ∀ i, Finset (G i),
        (∀ i, IsLocalFiniteApproximateGroup (L i) J (B i) ∧ η*(A i).card ≤ (B i).card ∧
          (∀ n ≤ 200, (L i).wordPower (B i : Set (G i)) n ⊆ (D i).small) ∧
          (D i).small ⊆ {x | (L i).escapeNorm (A i) x < r} ∧
          IsLocalFiniteApproximateGroup (D i).algebra J ((D i).finiteImage (B i)) ∧
          η*(A i).card ≤ ((D i).finiteImage (B i)).card * ((P i).card : ℝ)) ∧
        ∃ hDW : ∀ x ∈ (LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).small,
          π.toFun x ∈ W,
        ∃ C : Set W, IsCompact C ∧
          (∀ x : (LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).small,
            (⟨π.toFun x.val,hDW x.val x.property⟩ : W) ∈ C) ∧
          ∀ a : (LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).small,
            ((LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).modelQuotientHom
              hQ hW1 hWi hW6 π hPQ hDW).toFun
                ((LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D).project a) =
              (hQ.quotientAlgebra hW1 hWi hW6).one ↔ π.toFun a.val ∈ Q := by
  obtain ⟨Z,hZ,hZ1,hZW⟩ := exists_compact_subset hWo hW1
  obtain ⟨ε,hε,hsmall⟩ := local_model_escape_sublevel_small U G L (fun i => (A i : Set (G i)))
    (Filter.Eventually.of_forall fun i => (hA i).approximate.one_mem) π V hV hNSS himage (interior Z) isOpen_interior hZ1
  let ρ := min r ε
  have hρ : 0 < ρ := lt_min hr0 hε
  obtain ⟨J,η,hJ,hη,hquot⟩ := local_finite_central_quotient_of_set K hK ρ hρ
  have hP' : ∀ i, (L i).CentralLocalSet (P i : Set (G i))
      {x | (L i).escapeNorm (A i) x < 1/1001} {x | (L i).escapeNorm (A i) x < ρ} := by
    intro i
    refine ⟨(hP i).one_mem,(hP i).inv_mem,(hP i).mul_mem,?_⟩
    intro p hp x hx
    change (L i).escapeNorm (A i) x < ρ at hx
    exact (hP i).central p hp x (show (L i).escapeNorm (A i) x < r from hx.trans_le (min_le_left _ _))
  choose D B hB hBd hBsmall hDsmall hQB hDdiv hDrev hcard using
    fun i => hquot (G i) (L i) (hd i) (hr i) (A i) (hA i) (P i) (hP' i)
  let E := LocalGroupAlgebra.CentralQuotientData.ultraproduct U G L (fun i => (P i : Set (G i))) D
  have hEZ : ∀ x ∈ E.small, π.toFun x ∈ Z := by
    intro x hx
    apply interior_subset
    apply hsmall x
    have hsub : localUltraSet (U : Filter ι) G (fun i => (D i).small) ⊆
        localUltraSet (U : Filter ι) G (fun i => {z | (L i).escapeNorm (A i) z < ε}) :=
      (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).2
        (Filter.Eventually.of_forall fun i z hz => by
          have hh : (L i).escapeNorm (A i) z < ρ := hDsmall i hz
          exact show (L i).escapeNorm (A i) z < ε from hh.trans_le (min_le_right _ _))
    exact hsub hx
  have hEW : ∀ x ∈ E.small, π.toFun x ∈ W := fun x hx => hZW (hEZ x hx)
  let C : Set W := Subtype.val ⁻¹' Z
  have hC : IsCompact C := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    · exact hZ
    · simpa only [Subtype.range_coe] using hZW
  refine ⟨J,η,hJ,hη,D,B,fun i => ⟨hB i,hBd i,hBsmall i,?_,hQB i,hcard i⟩,
    hEW,C,hC,fun x => hEZ x.val x.property,?_⟩
  · intro x hx
    have hh : (L i).escapeNorm (A i) x < ρ := hDsmall i hx
    exact hh.trans_le (min_le_left _ _)
  · intro a
    exact E.modelQuotientHom_kernel hQ hW1 hWi hW6 π hPQ hEW a
end DirectedCycles
