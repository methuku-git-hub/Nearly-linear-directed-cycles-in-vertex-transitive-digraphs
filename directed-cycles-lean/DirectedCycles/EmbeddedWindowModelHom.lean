import DirectedCycles.GlobalWindowModelHom
import DirectedCycles.InternalFiniteAlong

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]
    {S : Type*} [Group S] (e : S →* GroupUltraproduct (U : Filter ι) G)
    (he : Function.Injective e)

/-- The literal range equivalence of an injective source homomorphism. -/
noncomputable def embeddedSourceRangeEquiv : S ≃* e.range :=
  MulEquiv.ofBijective e.rangeRestrict
    ⟨fun _ _ h => he (congrArg Subtype.val h),e.rangeRestrict_surjective⟩

theorem embeddedSourceRangeEquiv_apply (x : S) :
    (embeddedSourceRangeEquiv U G e he x).val = e x := rfl

theorem embeddedSourceRangeEquiv_symm_apply (y : e.range) :
    e ((embeddedSourceRangeEquiv U G e he).symm y) = y.val := by
  have h := congrArg Subtype.val ((embeddedSourceRangeEquiv U G e he).apply_symm_apply y)
  exact h

variable (W : ∀ i, Set (G i)) (h1 : ∀ i, (1 : G i) ∈ W i)
    (hi : ∀ i, ∀ x ∈ W i, x⁻¹ ∈ W i)
    (hWS : ultraSet (U : Filter ι) G W ⊆ e.range)

/-- Actual map from a finite-window reduced product to any embedded source,
including sources obtained by several successive subgroup restrictions. -/
noncomputable def ultraWindowEmbeddedHom :=
  (LocalGroupHom.ofMonoidHom (embeddedSourceRangeEquiv U G e he).symm.toMonoidHom).comp
    (ultraWindowSubgroupHom (U : Filter ι) G W h1 hi e.range hWS)

theorem ultraWindowEmbeddedHom_embedding (x : LocalUltraproduct (U : Filter ι) (fun i => W i)) :
    e ((ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun x) =
      (ultraWindowGroupHom (U : Filter ι) G W h1 hi).toFun x :=
  embeddedSourceRangeEquiv_symm_apply U G e he _

theorem ultraWindowEmbeddedHom_range :
    Set.range (ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun =
      e ⁻¹' ultraSet (U : Filter ι) G W := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,rfl⟩
    change e ((ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun y) ∈ ultraSet (U : Filter ι) G W
    rw [ultraWindowEmbeddedHom_embedding]
    exact (ultraWindowMap (U : Filter ι) G W y).property
  · intro x hx
    have hm : e x ∈ Set.range (ultraWindowGroupHom (U : Filter ι) G W h1 hi).toFun := by
      rw [ultraWindowGroupHom_range]
      exact hx
    obtain ⟨y,hy⟩ := hm
    refine ⟨y,he ?_⟩
    rw [ultraWindowEmbeddedHom_embedding,hy]

theorem ultraWindowEmbeddedHom_internal_preimage (B : ∀ i, Set (G i)) :
    (ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun ⁻¹'
      (e ⁻¹' ultraSet (U : Filter ι) G B) =
      localUltraSet (U : Filter ι) (fun i => W i) (fun i => Subtype.val ⁻¹' B i) := by
  rw [← ultraWindowGroupHom_internal_preimage (U : Filter ι) G W h1 hi B]
  ext x
  change e ((ultraWindowEmbeddedHom U G e he W h1 hi hWS).toFun x) ∈ ultraSet (U : Filter ι) G B ↔
    (ultraWindowGroupHom (U : Filter ι) G W h1 hi).toFun x ∈ ultraSet (U : Filter ι) G B
  rw [ultraWindowEmbeddedHom_embedding]

noncomputable def embeddedWindowModelHom {H : Type*} [Group H] (π : S →* H) :=
  (LocalGroupHom.ofMonoidHom π).comp (ultraWindowEmbeddedHom U G e he W h1 hi hWS)
end DirectedCycles
