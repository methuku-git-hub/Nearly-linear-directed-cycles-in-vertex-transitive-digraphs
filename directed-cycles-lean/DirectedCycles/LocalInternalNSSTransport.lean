module

public import DirectedCycles.LocalInternalSubgroups
public import DirectedCycles.LocalSubgroupTransport

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Internal NSS transports through an actual local-group equivalence.
Internal sets in the target are precisely the images of the indicated
component internal sets; no assertion about external subgroups is made. -/
theorem local_internal_nss_image_equiv {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i)) (A : ∀ i, Set (G i)) (hNSS : LocalInternalNSS G L U A)
    {Q : Type*} (M : LocalGroupAlgebra Q) (e : LocalUltraproduct (U : Filter ι) G ≃ Q)
    (f : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    (g : LocalGroupHom M (localUltraAlgebra (U : Filter ι) G L))
    (hf : f.toFun = e) (hg : g.toFun = e.symm) :
    ∀ H : ∀ i, Set (G i), M.IsGlobalSubgroup (e '' localUltraSet (U : Filter ι) G H) →
      e '' localUltraSet (U : Filter ι) G H ⊆ e '' localUltraSet (U : Filter ι) G A →
      e '' localUltraSet (U : Filter ι) G H ⊆ {M.one} := by
  intro H hH hHA
  have himage := hH.image g
  have he : e.symm '' (e '' localUltraSet (U : Filter ι) G H) = localUltraSet (U : Filter ι) G H := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa only [e.symm_apply_apply] using hz
    · exact fun hx => ⟨e x,⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
  have hsubgroup : (localUltraAlgebra (U : Filter ι) G L).IsGlobalSubgroup (localUltraSet (U : Filter ι) G H) := by
    simpa only [hg,he] using himage
  have hsub : localUltraSet (U : Filter ι) G H ⊆ localUltraSet (U : Filter ι) G A := by
    intro x hx
    obtain ⟨y,hy,heq⟩ := hHA ⟨x,hx,rfl⟩
    exact e.injective heq ▸ hy
  rintro x ⟨a,ha,rfl⟩
  have ha1 : a = (localUltraAlgebra (U : Filter ι) G L).one := hNSS H hsubgroup hsub ha
  rw [ha1]
  exact hf ▸ f.map_one
end DirectedCycles
