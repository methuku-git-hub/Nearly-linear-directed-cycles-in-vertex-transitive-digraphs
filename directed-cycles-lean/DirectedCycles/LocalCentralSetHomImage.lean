module

public import DirectedCycles.LocalCentralEquivalence
public import DirectedCycles.LocalGroupHom

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} {L : LocalGroupAlgebra G} {Q : LocalGroupAlgebra H}

/-- Actual central local sets descend through a local homomorphism when the
specified product and preimage domains are available. -/
theorem CentralLocalSet.hom_image {P V S : Set G} (hP : L.CentralLocalSet P V S)
    (π : LocalGroupHom L Q) (V' S' : Set H)
    (hdom : ∀ x ∈ P, ∀ y ∈ P, L.Defined x y)
    (hsmall : ∀ z, π.toFun z ∈ V' → z ∈ V)
    (hthick : S' ⊆ π.toFun '' S) :
    Q.CentralLocalSet (π.toFun '' P) V' S' where
  one_mem := ⟨L.one,hP.one_mem,π.map_one⟩
  inv_mem := by
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨L.inv p,hP.inv_mem p hp,π.map_inv p⟩
  mul_mem := by
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ z hz hmul
    obtain ⟨c,hc⟩ := hdom p hp q hq
    have he : π.toFun c = z := Q.unique (π.map_mul hc) hmul
    exact ⟨c,hP.mul_mem p hp q hq c (hsmall c (he.symm ▸ hz)) hc,he⟩
  central := by
    rintro _ ⟨p,hp,rfl⟩ x hx
    obtain ⟨y,hy,rfl⟩ := hthick hx
    obtain ⟨z,hpz,hyp⟩ := hP.central p hp y hy
    exact ⟨π.toFun z,π.map_mul hpz,π.map_mul hyp⟩
end LocalGroupAlgebra
end DirectedCycles
