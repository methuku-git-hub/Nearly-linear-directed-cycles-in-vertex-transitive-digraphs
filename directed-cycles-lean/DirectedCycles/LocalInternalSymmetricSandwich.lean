module

public import DirectedCycles.LocalConjugateTransfer
public import DirectedCycles.LocalGroupHom

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι H : Type*} [Group H] (U : Ultrafilter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i))

/-- Componentwise symmetrization preserves a symmetric inner model
preimage and the outer containment, with exact finite representatives. -/
theorem local_internal_symmetric_sandwich
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (F V : Set H) (hF : ∀ x ∈ F, x⁻¹ ∈ F) (B : ∀ i, Finset (G i))
    (hinner : π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (houter : localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π.toFun ⁻¹' V) :
    ∃ A : ∀ i, Finset (G i),
      (∀ i, ∀ x ∈ A i, (L i).inv x ∈ A i) ∧
      π.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ∧
      localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) ⊆ π.toFun ⁻¹' V := by
  classical
  let A : ∀ i, Finset (G i) := fun i => (B i).filter (fun x => (L i).inv x ∈ B i)
  let B' := localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i)))
  have heq : localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) =
      B' ∩ (localUltraAlgebra (U : Filter ι) G L).inv ⁻¹' B' := by
    ext x
    obtain ⟨a,rfl⟩ := Quotient.exists_rep x
    simp only [A,B',Set.mem_inter_iff,Set.mem_preimage,localUltra_inv_mk_filter,
      localUltraMk_mem_iff,Finset.mem_coe,Finset.mem_filter,Filter.eventually_and]
  refine ⟨A,?_,?_,?_⟩
  · intro i x hx
    obtain ⟨hx,hix⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hix,by simpa only [(L i).inv_inv] using hx⟩
  · intro x hx
    rw [heq]
    refine ⟨hinner hx,hinner ?_⟩
    change π.toFun ((localUltraAlgebra (U : Filter ι) G L).inv x) ∈ F
    rw [π.map_inv]
    exact hF _ hx
  · rw [heq]
    exact fun _ hx => houter hx.1
end DirectedCycles
