module

public import DirectedCycles.LocalLargeIndex
public import DirectedCycles.LocalScaledPowers
public import DirectedCycles.LocalCentralQuotientData

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (s : Set ι) (hs : s ∈ U)
    (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

theorem localLargeIndex_restrict_scaledPower (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i)) (t : ℝ) :
    (localLargeIndexRestrict U s hs G L).toFun (localScaledPower U G L u N M p t) =
      localScaledPower (localLargeIndexUltrafilter U s hs) (fun j => G j.val) (fun j => L j.val)
        (fun j => u j.val) (fun j => N j.val) (fun j => M j.val) (fun j => p j.val) t := rfl

theorem localLargeIndex_extend_scaledPower (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i)) (t : ℝ) :
    (localLargeIndexExtend U s hs G L).toFun
      (localScaledPower (localLargeIndexUltrafilter U s hs) (fun j => G j.val) (fun j => L j.val)
        (fun j => u j.val) (fun j => N j.val) (fun j => M j.val) (fun j => p j.val) t) =
      localScaledPower U G L u N M p t := localLargeIndex_extend_restrict U s hs G L (localScaledPower U G L u N M p t)

/-- Restricting the index set preserves the exact model image of every
internal set, not only its containment in a target neighbourhood. -/
theorem localLargeIndex_model_image {H : Type*} (M : LocalGroupAlgebra H)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M) (A : ∀ i, Set (G i)) :
    (π.comp (localLargeIndexExtend U s hs G L)).toFun ''
        localUltraSet (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val) (fun j => A j.val) =
      π.toFun '' localUltraSet (U : Filter ι) G A := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(localLargeIndexExtend U s hs G L).toFun x,(localLargeIndex_extend_mem U s hs G L A x).2 hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(localLargeIndexRestrict U s hs G L).toFun x,(localLargeIndex_restrict_mem U s hs G L A x).2 hx,?_⟩
    change π.toFun ((localLargeIndexExtend U s hs G L).toFun ((localLargeIndexRestrict U s hs G L).toFun x)) = _
    rw [localLargeIndex_extend_restrict]

/-- The quotient-model kernel condition survives restriction to a large
index set. Actual source and projected representatives are extended by their
identities, and both resulting equalities are proved on that large set. -/
theorem localLargeIndex_component_kernel {H T : Type*} (M : LocalGroupAlgebra H) (Q : LocalGroupAlgebra T)
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    (Ψ : LocalGroupHom (localUltraAlgebra (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).algebra)) Q)
    (hkernel : ∀ a : ∀ i, (D i).small,
      Ψ.toFun (localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (a i))) = Q.one →
      π.toFun (localUltraMk (U : Filter ι) G (fun i => (a i).val)) ∈ π.toFun '' localUltraSet (U : Filter ι) G P) :
    ∀ a : ∀ j : s, (D j.val).small,
      (Ψ.comp (localLargeIndexExtend U s hs (fun i => (D i).Carrier) (fun i => (D i).algebra))).toFun
        (localUltraMk (localLargeIndexUltrafilter U s hs : Filter s) (fun j => (D j.val).Carrier)
          (fun j => (D j.val).project (a j))) = Q.one →
      (π.comp (localLargeIndexExtend U s hs G L)).toFun
        (localUltraMk (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val) (fun j => (a j).val)) ∈
      (π.comp (localLargeIndexExtend U s hs G L)).toFun ''
        localUltraSet (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val) (fun j => P j.val) := by
  classical
  intro a ha
  let b : ∀ i, (D i).small := fun i => if hi : i ∈ s then a ⟨i,hi⟩ else ⟨(L i).one,(D i).one_mem⟩
  have hp : localUltraMk (U : Filter ι) (fun i => (D i).Carrier) (fun i => (D i).project (b i)) =
      (localLargeIndexExtend U s hs (fun i => (D i).Carrier) (fun i => (D i).algebra)).toFun
        (localUltraMk (localLargeIndexUltrafilter U s hs : Filter s) (fun j => (D j.val).Carrier)
          (fun j => (D j.val).project (a j))) := by
    apply Quotient.sound
    filter_upwards [hs] with i hi
    simp only [b,dite_eq_left hi]
  have hv : localUltraMk (U : Filter ι) G (fun i => (b i).val) =
      (localLargeIndexExtend U s hs G L).toFun
        (localUltraMk (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val) (fun j => (a j).val)) := by
    apply Quotient.sound
    filter_upwards [hs] with i hi
    simp only [b,dite_eq_left hi]
  have hk := hkernel b (by rw [hp]; exact ha)
  rw [hv] at hk
  rw [localLargeIndex_model_image]
  exact hk
end DirectedCycles
