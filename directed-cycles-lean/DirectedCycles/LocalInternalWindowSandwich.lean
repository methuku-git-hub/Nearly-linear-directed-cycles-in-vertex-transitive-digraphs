module

public import DirectedCycles.LocalInternalImages
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Restricting the actual component source windows and an open model
window preserves internal compact/open approximation. The finite witnesses
are obtained by restricting the original finite witnesses componentwise. -/
theorem local_internal_window_sandwich {ι : Type*} (U : Ultrafilter ι)
    (G : ι → Type*) (S : ∀ i, Set (G i))
    {H : Type*} [TopologicalSpace H] (W : Set H) (hW : IsOpen W)
    (π : LocalUltraproduct (U : Filter ι) G → H)
    (π' : LocalUltraproduct (U : Filter ι) (fun i => S i) → W)
    (hcomm : ∀ x, (π' x).val = π (localUltraMap (U : Filter ι) (fun i => S i) G (fun _ => Subtype.val) x))
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V → V ⊆ W →
      ∃ B : ∀ i, Finset (G i),
        π ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π ⁻¹' V) :
    ∀ F V : Set W, IsCompact F → IsOpen V → F ⊆ V →
      ∃ B : ∀ i, Finset (S i),
        π' ⁻¹' F ⊆ localUltraSet (U : Filter ι) (fun i => S i) (fun i => (B i : Set (S i))) ∧
        localUltraSet (U : Filter ι) (fun i => S i) (fun i => (B i : Set (S i))) ⊆ π' ⁻¹' V := by
  classical
  intro F V hF hV hFV
  obtain ⟨A,hAin,hAout⟩ := hsandwich (Subtype.val '' F) (Subtype.val '' V)
    (hF.image continuous_subtype_val) (hW.isOpenMap_subtype_val V hV) (Set.image_mono hFV)
    (by rintro _ ⟨x,_,rfl⟩; exact x.property)
  let B : ∀ i, Finset (S i) := fun i => (A i).subtype (· ∈ S i)
  have hmem : ∀ x : LocalUltraproduct (U : Filter ι) (fun i => S i),
      x ∈ localUltraSet (U : Filter ι) (fun i => S i) (fun i => (B i : Set (S i))) ↔
      localUltraMap (U : Filter ι) (fun i => S i) G (fun _ => Subtype.val) x ∈
        localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))) := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      change localUltraMk _ _ a ∈ _ ↔ localUltraMk _ _ (fun i => (a i).val) ∈ _
      simp only [localUltraMk_mem_iff,B,Finset.mem_coe,Finset.mem_subtype]
  refine ⟨B,?_,?_⟩
  · intro x hx
    apply (hmem x).2
    exact hAin ⟨π' x,hx,hcomm x⟩
  · intro x hx
    obtain ⟨y,hy,he⟩ := hAout ((hmem x).1 hx)
    have he' : y = π' x := Subtype.ext (he.trans (hcomm x).symm)
    change π' x ∈ V
    rw [← he']
    exact hy
end DirectedCycles
