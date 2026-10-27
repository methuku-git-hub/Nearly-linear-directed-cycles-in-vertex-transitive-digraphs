module

public import DirectedCycles.EmbeddedWindowModelHom
public import DirectedCycles.InternalGoodModel

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
universe u
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]
    {S : Type u} [Group S] (e : S →* GroupUltraproduct (U : Filter ι) G)
    (he : Function.Injective e)
    (W : ∀ i, Set (G i)) (h1 : ∀ i, (1 : G i) ∈ W i)
    (hi : ∀ i, ∀ x ∈ W i, x⁻¹ ∈ W i)
    (hWS : ultraSet (U : Filter ι) G W ⊆ e.range)
    {T : Set S} {Internal : Set S → Prop}
    (M : InternalLocallyCompactGroupModel S T Internal)

/-- The actual finite-window model retains compact/open internal
approximation from its global good model. The component sets are intersected
with the windows explicitly using finite subtype preimages. -/
theorem embedded_window_model_sandwich
    (hI : ∀ B : Set S, Internal B → IsInternalFiniteAlong U G e B)
    (F O : Set M.carrier) (hF : IsCompact F) (hO : IsOpen O)
    (hFO : F ⊆ O) (hOU : O ⊆ M.neighbourhood) :
    ∃ B : ∀ i, Finset (W i),
      (embeddedWindowModelHom U G e he W h1 hi hWS M.map).toFun ⁻¹' F ⊆
        localUltraSet (U : Filter ι) (fun i => W i) (fun i => (B i : Set (W i))) ∧
      localUltraSet (U : Filter ι) (fun i => W i) (fun i => (B i : Set (W i))) ⊆
        (embeddedWindowModelHom U G e he W h1 hi hWS M.map).toFun ⁻¹' O := by
  classical
  obtain ⟨D,hD,hFD,hDO⟩ := M.internal_sandwich F O hF hO hFO hOU
  obtain ⟨B,hDB⟩ := hI D hD
  let B' : ∀ i, Finset (W i) := fun i =>
    @Finset.subtype (G i) (fun x => x ∈ W i) (fun _ => Classical.propDecidable _) (B i)
  have hB' : ∀ i, (B' i : Set (W i)) = Subtype.val ⁻¹' (B i : Set (G i)) := by
    intro i
    ext x
    simp only [B',Finset.mem_coe,Finset.mem_subtype,Set.mem_preimage]
  have hpre : (ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun ⁻¹' D =
      localUltraSet (U : Filter ι) (fun i => W i) (fun i => (B' i : Set (W i))) := by
    rw [hDB,ultraWindowEmbeddedHom_internal_preimage]
    simp only [hB']
  refine ⟨B',?_,?_⟩
  · rw [← hpre]
    exact Set.preimage_mono hFD
  · rw [← hpre]
    exact Set.preimage_mono hDO

/-- The good-model small neighbourhood remains small on the finite-window
source, with an exact component description of the bounding set. -/
theorem embedded_window_model_small (A : ∀ i, Set (G i))
    (hTA : T ⊆ e ⁻¹' ultraSet (U : Filter ι) G A) :
    (embeddedWindowModelHom U G e he W h1 hi hWS M.map).toFun ⁻¹' M.neighbourhood ⊆
      localUltraSet (U : Filter ι) (fun i => W i) (fun i => Subtype.val ⁻¹' A i) := by
  rw [← ultraWindowEmbeddedHom_internal_preimage U G e he W h1 hi hWS A]
  exact Set.preimage_mono (M.small_neighbourhood.trans hTA)

/-- Thickness is retained when the actual modelled source set lies in the
chosen internal window. Every lifted point is in the stated finite-window
source; no extension of a partial model map is used. -/
theorem embedded_window_model_thick
    (hTW : T ⊆ e ⁻¹' ultraSet (U : Filter ι) G W) :
    M.neighbourhood ⊆ Set.range (embeddedWindowModelHom U G e he W h1 hi hWS M.map).toFun := by
  intro y hy
  obtain ⟨s,hs,heq⟩ := M.thick_neighbourhood hy
  have hm : s ∈ Set.range (ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun := by
    rw [ultraWindowEmbeddedHom_range]
    exact hTW hs
  obtain ⟨x,hx⟩ := hm
  refine ⟨x,?_⟩
  change M.map ((ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun x) = y
  rw [hx,heq]

/-- A bounded component set has image inside the same actual compact
model image as the global source set. -/
theorem embedded_window_model_compact_control (A : ∀ i, Set (G i))
    (hAT : e ⁻¹' ultraSet (U : Filter ι) G A ⊆ T) :
    (embeddedWindowModelHom U G e he W h1 hi hWS M.map).toFun ''
      localUltraSet (U : Filter ι) (fun i => W i) (fun i => Subtype.val ⁻¹' A i) ⊆ M.map '' T := by
  rw [← ultraWindowEmbeddedHom_internal_preimage U G e he W h1 hi hWS A]
  rintro y ⟨x,hx,rfl⟩
  exact ⟨(ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun x,hAT hx,rfl⟩
end DirectedCycles
