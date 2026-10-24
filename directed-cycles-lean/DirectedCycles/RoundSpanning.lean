import DirectedCycles.RoundCycleExpansion
import DirectedCycles.FullCosetSpanning

set_option autoImplicit false
namespace DirectedCycles

/-- Right translates of a spanning set still span; containment in a larger
set suffices. This uses the actual integral truncated group ring. -/
theorem spansTruncation_of_right_translate {G : Type*} [Group G] (D : ℕ)
    (E F : Set G) (y : G) (hE : SpansTruncation D E)
    (hEF : ∀ x ∈ E, x*y ∈ F) : SpansTruncation D F := by
  let W := AddSubgroup.closure (truncatedElement G D '' F)
  let φ := AddMonoidHom.mulRight (truncatedElement G D y)
  have hmap : ∀ x ∈ E, φ (truncatedElement G D x) ∈ W := by
    intro x hx
    change truncatedElement G D x * truncatedElement G D y ∈ W
    rw [← map_mul]
    exact AddSubgroup.subset_closure ⟨x*y,hEF x hx,rfl⟩
  have hall : ∀ x : G, truncatedElement G D x ∈ W := by
    intro x
    have h := spansTruncation_map_mem D E hE φ W hmap (truncatedElement G D (x*y⁻¹))
    change truncatedElement G D (x*y⁻¹) * truncatedElement G D y ∈ W at h
    rwa [← map_mul,inv_mul_cancel_right] at h
  apply top_le_iff.mp
  rw [← truncated_elements_generate (G := G) D]
  exact W.closure_le.mpr (by rintro x ⟨g,rfl⟩; exact hall g)

/-- Left translation also preserves integral additive generation. -/
theorem spansTruncation_of_left_translate {G : Type*} [Group G] (D : ℕ)
    (E F : Set G) (y : G) (hE : SpansTruncation D E)
    (hEF : ∀ x ∈ E, y*x ∈ F) : SpansTruncation D F := by
  let W := AddSubgroup.closure (truncatedElement G D '' F)
  let φ := AddMonoidHom.mulLeft (truncatedElement G D y)
  have hmap : ∀ x ∈ E, φ (truncatedElement G D x) ∈ W := by
    intro x hx
    change truncatedElement G D y * truncatedElement G D x ∈ W
    rw [← map_mul]
    exact AddSubgroup.subset_closure ⟨y*x,hEF x hx,rfl⟩
  have hall : ∀ x : G, truncatedElement G D x ∈ W := by
    intro x
    have h := spansTruncation_map_mem D E hE φ W hmap (truncatedElement G D (y⁻¹*x))
    change truncatedElement G D y * truncatedElement G D (y⁻¹*x) ∈ W at h
    rwa [← map_mul,mul_inv_cancel_left] at h
  apply top_le_iff.mp
  rw [← truncated_elements_generate (G := G) D]
  exact W.closure_le.mpr (by rintro x ⟨g,rfl⟩; exact hall g)

/-- The full round-expansion invariant used in the nilpotent induction. -/
theorem expand_cycle_into_rounds_spanning {G : Type*} [Group G] {T : ℕ} [NeZero T]
    (S : ZMod T → Set G) (xs : List G) (hlen : xs.length = T)
    (hxs : LayerWord S 0 xs) (C : Cycle (CayleyDigraph (singleRoundProducts S xs)))
    (hC : C.ClosedUnderGenerator xs.prod) :
    ∃ L : Cycle (CyclicLayerDigraph S), L.length = T*C.length ∧
      ∀ D : ℕ, SpansTruncation D (C.generatorTails xs.prod) →
        ∀ z : ZMod T, SpansTruncation D (L.layerCoordinates z) := by
  obtain ⟨L,hL,htails⟩ := expand_cycle_into_rounds S xs hlen hxs C hC
  refine ⟨L,hL,?_⟩
  intro D hD z
  exact spansTruncation_of_right_translate D _ _ (xs.take z.val).prod hD (htails z)

end DirectedCycles
