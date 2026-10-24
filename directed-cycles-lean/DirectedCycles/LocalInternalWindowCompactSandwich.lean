import DirectedCycles.LocalInternalImages
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

set_option autoImplicit false
namespace DirectedCycles

/-- Internal approximation on a local model neighbourhood suffices for
an open target window of any size, provided the restricted source image lies
in a compact subset of that model neighbourhood. No larger neighbourhood
sandwich property is assumed. -/
theorem local_internal_window_sandwich_of_compact_range {ι : Type*} (U : Ultrafilter ι)
    (G : ι → Type*) (S : ∀ i, Set (G i))
    {H : Type*} [TopologicalSpace H] [T2Space H] (W : Set H) (hW : IsOpen W)
    (π : LocalUltraproduct (U : Filter ι) G → H)
    (π' : LocalUltraproduct (U : Filter ι) (fun i => S i) → W)
    (hcomm : ∀ x, (π' x).val = π (localUltraMap (U : Filter ι) (fun i => S i) G (fun _ => Subtype.val) x))
    (C U₀ : Set H) (hC : IsCompact C) (hU₀ : IsOpen U₀) (hCU₀ : C ⊆ U₀)
    (hπC : ∀ x, (π' x).val ∈ C)
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V → V ⊆ U₀ →
      ∃ B : ∀ i, Finset (G i),
        π ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
        localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ π ⁻¹' V) :
    ∀ F V : Set W, IsCompact F → IsOpen V → F ⊆ V →
      ∃ B : ∀ i, Finset (S i),
        π' ⁻¹' F ⊆ localUltraSet (U : Filter ι) (fun i => S i) (fun i => (B i : Set (S i))) ∧
        localUltraSet (U : Filter ι) (fun i => S i) (fun i => (B i : Set (S i))) ⊆ π' ⁻¹' V := by
  classical
  intro F V hF hV hFV
  obtain ⟨A,hAin,hAout⟩ := hsandwich (C ∩ Subtype.val '' F) (U₀ ∩ Subtype.val '' V)
    (hC.inter_right (hF.image continuous_subtype_val).isClosed)
    (hU₀.inter (hW.isOpenMap_subtype_val V hV))
    (fun _ hx => ⟨hCU₀ hx.1,Set.image_mono hFV hx.2⟩) Set.inter_subset_left
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
    apply hAin
    refine ⟨?_,π' x,hx,hcomm x⟩
    rw [← hcomm x]
    exact hπC x
  · intro x hx
    obtain ⟨y,hy,he⟩ := (hAout ((hmem x).1 hx)).2
    have he' : y = π' x := Subtype.ext (he.trans (hcomm x).symm)
    change π' x ∈ V
    rw [← he']
    exact hy
end DirectedCycles
