module

public import DirectedCycles.LocalGlobalSubgroup
public import DirectedCycles.LocalEscapeNorm
public import DirectedCycles.LocalGroupCongruence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G J : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra J}

/-- The image of an actual global subgroup under a local homomorphism is
again a global subgroup: totality comes from multiplying source representatives. -/
theorem IsGlobalSubgroup.image {H : Set G} (hH : L.IsGlobalSubgroup H)
    (f : LocalGroupHom L M) : M.IsGlobalSubgroup (f.toFun '' H) where
  one_mem := ⟨L.one,hH.one_mem,f.map_one⟩
  inv_mem := by
    rintro x ⟨a,ha,rfl⟩
    exact ⟨L.inv a,hH.inv_mem a ha,f.map_inv a⟩
  mul_total := by
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
    obtain ⟨c,hc,hm⟩ := hH.mul_total a ha b hb
    exact ⟨f.toFun c,⟨c,hc,rfl⟩,f.map_mul hm⟩

/-- Every power of a subgroup element is genuinely defined, with all
bracketings, and remains in that subgroup. -/
theorem IsGlobalSubgroup.powerIn {H : Set G} (hH : L.IsGlobalSubgroup H)
    {g : G} (hg : g ∈ H) (n : ℕ) : L.PowerIn H g n := by
  let := hH.toGroup
  let gH : H := ⟨g,hg⟩
  refine ⟨(gH^n).val,(gH^n).property,?_⟩
  have hp := (ofGroup_product H (List.replicate n gH)).map hH.inclusionHom
  simpa [IsGlobalSubgroup.inclusionHom,gH] using hp

theorem IsGlobalSubgroup.escapeNorm_eq_zero {H A : Set G}
    (hH : L.IsGlobalSubgroup H) (hHA : H ⊆ A) (hA : L.one ∈ A)
    {g : G} (hg : g ∈ H) : L.escapeNorm A g = 0 := by
  apply (L.escapeNorm_eq_zero_iff hA g).2
  intro n
  obtain ⟨x,hx,hp⟩ := hH.powerIn hg n
  exact ⟨x,hHA hx,hp⟩
end LocalGroupAlgebra

namespace LocalGroupCongruence
variable {G : Type*} {L : LocalGroupAlgebra G} (C : LocalGroupCongruence L)

/-- Product-domain transport makes the full inverse image of a global
subgroup a genuine global subgroup of the original local group. -/
theorem preimage_isGlobalSubgroup {H : Set C.Carrier} (hH : C.algebra.IsGlobalSubgroup H) :
    L.IsGlobalSubgroup (C.project ⁻¹' H) where
  one_mem := hH.one_mem
  inv_mem := by
    intro a ha
    exact hH.inv_mem (C.project a) ha
  mul_total := by
    intro a ha b hb
    obtain ⟨c,hc,hm⟩ := hH.mul_total (C.project a) ha (C.project b) hb
    obtain ⟨d,hd,hm'⟩ := C.lift_mul hm
    refine ⟨d,?_,hm'⟩
    change C.project d ∈ H
    rw [hd]
    exact hc
end LocalGroupCongruence
end DirectedCycles
