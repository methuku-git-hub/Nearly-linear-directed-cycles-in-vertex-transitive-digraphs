import DirectedCycles.GlobalGoodModelKernelWindows
import DirectedCycles.GlobalWindowFiniteDomains
import DirectedCycles.EmbeddedWindowGoodModel
import DirectedCycles.LocalSmoothModelData

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Pointwise Topology
namespace DirectedCycles
namespace GlobalGoodModelKernelWindows
variable {u : Ultrafilter ℕ} {G : ℕ → Type*} [∀ i, Group (G i)] [∀ i, DecidableEq (G i)]
    {A : ∀ i, Finset (G i)}
    {M : let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
      let H := Subgroup.closure B
      InternalLocallyCompactGroupModel H (H.subtype ⁻¹' (B^4)) (IsInternalFiniteIn u G H)}
    {D : LieQuotientData M.carrier M.neighbourhood}
    (C : GlobalGoodModelKernelWindows u G A M D)

abbrev windowAlgebra (i : ℕ) : LocalGroupAlgebra (C.W i : Set (G i)) :=
  (LocalGroupAlgebra.ofGroup (G i)).restrict (C.W i : Set (G i)) (C.W_data i).1 (C.W_data i).2.1

noncomputable def finiteSource (i : ℕ) : Finset (C.W i : Set (G i)) :=
  finiteWindowSource (C.W i : Set (G i)) (C.B i)

/-- The initial compact-kernel Lie quotient supplies an actual homomorphism
on the internal finite domain windows, with compact image, small and thick
neighbourhood, and full compact/open internal approximation. -/
theorem exists_local_model :
    Nonempty (LocalSmoothModelData u (fun i => (C.W i : Set (G i))) C.windowAlgebra
      C.finiteSource (LocalGroupAlgebra.ofGroup (lieQuotientGoodModel M D).carrier)) := by
  classical
  let := D.normal
  let T := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
  let H := Subgroup.closure T
  let S := D.source.comap M.map
  let e : S →* GroupUltraproduct (u : Filter ℕ) G := H.subtype.comp S.subtype
  have he : Function.Injective e := H.subtype_injective.comp S.subtype_injective
  let W : ∀ i, Set (G i) := fun i => (C.W i : Set (G i))
  have hW1 : ∀ i, (1 : G i) ∈ W i := fun i => (C.W_data i).1
  have hWi : ∀ i, ∀ x ∈ W i, x⁻¹ ∈ W i := fun i => (C.W_data i).2.1
  have hTH : T^4 ⊆ (H : Set _) := by
    intro x hx
    obtain ⟨l,_hl,hm,heq⟩ := exists_list_of_mem_set_power hx
    rw [← heq]
    exact H.list_prod_mem (fun y hy => Subgroup.subset_closure (hm y hy))
  have hW4 : ultraSet (u : Filter ℕ) G W ⊆ T^4 := by
    rw [← ultraSet_pow]
    apply ultraSet_mono
    exact Filter.Eventually.of_forall fun i => by
      rw [← Finset.coe_pow]
      exact (C.W_data i).2.2
  have hWS : ultraSet (u : Filter ℕ) G W ⊆ e.range := by
    intro x hx
    let x' : H := ⟨x,hTH (hW4 hx)⟩
    have hxS : x' ∈ S := C.W_source hx
    exact ⟨⟨x',hxS⟩,rfl⟩
  let Q := lieQuotientGoodModel M D
  let π := embeddedWindowModelHom u G e he W hW1 hWi hWS Q.map
  have hI : ∀ B : Set S, RestrictedInternal S (IsInternalFiniteIn u G H) B →
      IsInternalFiniteAlong u G e B := by
    intro B hB
    exact (restricted_internal_finite_along u G H.subtype S B).1 hB
  obtain ⟨V,hVo,hV1,hVsmall⟩ := compact_kernel_quotient_small_preimage D.kernel
    D.compact_kernel (D.source.subtype ⁻¹' C.inner)
    (C.inner_open.preimage continuous_subtype_val) (by
      intro x hx
      exact C.kernel_inner ⟨x,hx,rfl⟩)
  let O : Set Q.carrier := V ∩ Q.neighbourhood
  have hOo : IsOpen O := hVo.inter Q.open_neighbourhood
  have hO1 : (1 : Q.carrier) ∈ O := ⟨hV1,Q.one_mem_neighbourhood⟩
  have hsmallS : Q.map ⁻¹' O ⊆ e ⁻¹' ultraSet (u : Filter ℕ) G (fun i => (C.B i : Set (G i))) := by
    intro x hx
    have hh : M.map x.val ∈ C.inner := hVsmall hx.1
    exact C.B_lower (subset_closure hh)
  have hB4 : ultraSet (u : Filter ℕ) G (fun i => (C.B i : Set (G i))) ⊆ T^4 := by
    rw [← ultraSet_pow]
    apply ultraSet_mono
    exact Filter.Eventually.of_forall fun i => by
      rw [← Finset.coe_pow]
      exact (C.B_data i).2.2
  have hsmall : π.toFun ⁻¹' O ⊆
      localUltraSet (u : Filter ℕ) (fun i => W i) (fun i => (C.finiteSource i : Set (W i))) := by
    simp only [finiteSource,finiteWindowSource_coe]
    rw [← ultraWindowEmbeddedHom_internal_preimage u G e he W hW1 hWi hWS]
    exact Set.preimage_mono hsmallS
  have hcompact := Q.compact_image
  have himage : ∀ z ∈ localUltraSet (u : Filter ℕ) (fun i => W i)
      (fun i => (C.finiteSource i : Set (W i))), π.toFun z ∈ Q.map '' (S.subtype ⁻¹' (H.subtype ⁻¹' (T^4))) := by
    intro z hz
    apply embedded_window_model_compact_control u G e he W hW1 hWi hWS Q
      (fun i => (C.B i : Set (G i))) (fun x hx => hB4 hx)
    exact ⟨z,by simpa only [finiteSource,finiteWindowSource_coe] using hz,rfl⟩
  have hBW : ultraSet (u : Filter ℕ) G (fun i => (C.B i : Set (G i))) ⊆ ultraSet (u : Filter ℕ) G W := by
    apply ultraSet_mono
    filter_upwards [C.products] with i hi
    exact (Set.subset_pow (C.B_data i).1 (by omega : 2 ≠ 0)).trans hi
  have hthick : ∀ y ∈ O, ∃ z, π.toFun z = y := by
    intro y hy
    obtain ⟨x,hxy⟩ := Q.surjective y
    have hxB : e x ∈ ultraSet (u : Filter ℕ) G (fun i => (C.B i : Set (G i))) :=
      hsmallS (show Q.map x ∈ O from hxy.symm ▸ hy)
    have hxrange : x ∈ Set.range (ultraWindowEmbeddedHom u G e he W hW1 hWi hWS).toFun := by
      rw [ultraWindowEmbeddedHom_range]
      exact hBW hxB
    obtain ⟨z,hzx⟩ := hxrange
    refine ⟨z,?_⟩
    change Q.map ((ultraWindowEmbeddedHom u G e he W hW1 hWi hWS).toFun z) = y
    rw [hzx,hxy]
  refine ⟨{
    map := π
    compactSet := Q.map '' (S.subtype ⁻¹' (H.subtype ⁻¹' (T^4)))
    compact := hcompact
    image := himage
    window := O
    window_open := hOo
    one_mem := hO1
    small := hsmall
    thick := hthick
    sandwich := ?_ }⟩
  intro F O' hF hO' hFO hO'O
  exact embedded_window_model_sandwich u G e he W hW1 hWi hWS Q hI F O' hF hO' hFO
    (hO'O.trans Set.inter_subset_right)
end GlobalGoodModelKernelWindows
end DirectedCycles
