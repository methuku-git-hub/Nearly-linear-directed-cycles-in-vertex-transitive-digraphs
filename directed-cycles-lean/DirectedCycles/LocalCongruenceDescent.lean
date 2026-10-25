module

public import DirectedCycles.LocalGroupCongruence
public import DirectedCycles.LocalNormalSubgroupQuotient
public import DirectedCycles.LocalSubgroupTransport

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupCongruence
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}
    (C : LocalGroupCongruence L)

/-- An actual local homomorphism constant on congruence classes descends to
an actual local homomorphism on the quotient. -/
def liftHom (f : LocalGroupHom L M)
    (hf : ∀ a b, C.toSetoid.r a b → f.toFun a = f.toFun b) : LocalGroupHom C.algebra M where
  toFun := Quotient.lift f.toFun hf
  map_one := f.map_one
  map_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact f.map_inv x
  map_mul := by
    rintro x y z ⟨a,b,c,rfl,rfl,rfl,hm⟩
    exact f.map_mul hm

theorem liftHom_project (f : LocalGroupHom L M)
    (hf : ∀ a b, C.toSetoid.r a b → f.toFun a = f.toFun b) (a : G) :
    (C.liftHom f hf).toFun (C.project a) = f.toFun a := rfl

theorem liftHom_surjective (f : LocalGroupHom L M)
    (hf : ∀ a b, C.toSetoid.r a b → f.toFun a = f.toFun b)
    (hs : Function.Surjective f.toFun) : Function.Surjective (C.liftHom f hf).toFun := by
  intro y
  obtain ⟨a,ha⟩ := hs y
  exact ⟨C.project a,ha⟩

theorem liftHom_image (f : LocalGroupHom L M)
    (hf : ∀ a b, C.toSetoid.r a b → f.toFun a = f.toFun b) (A : Set G) :
    (C.liftHom f hf).toFun '' (C.project '' A) = f.toFun '' A := by
  rw [Set.image_image]
  rfl
end LocalGroupCongruence

namespace LocalGroupAlgebra
namespace NormalSubgroupWindow
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H} {N S : Set G}
    (W : L.NormalSubgroupWindow N S) (hd : L.DivisionClosed) (hr : L.Reversible)

/-- Killing the actual normal subgroup makes the model map constant on all
local quotient classes. This is proved from the orbit relation and the
homomorphism law, with no assumed quotient map. -/
theorem model_constant_on_classes (f : LocalGroupHom W.restricted M)
    (hkill : ∀ h : S, h.val ∈ N → f.toFun h = M.one)
    (a b : S) (hab : W.relation a b) : f.toFun a = f.toFun b := by
  obtain ⟨h,hh,hm⟩ := hab
  let hS : S := ⟨h,W.subset hh⟩
  have hfm := f.map_mul (x := hS) hm
  rw [hkill hS hh] at hfm
  exact M.unique hfm (M.one_mul (f.toFun b))

def descendModel (f : LocalGroupHom W.restricted M)
    (hkill : ∀ h : S, h.val ∈ N → f.toFun h = M.one) :
    LocalGroupHom (W.congruence hd hr).algebra M :=
  (W.congruence hd hr).liftHom f (W.model_constant_on_classes f hkill)

/-- If the subgroup image lies in an NSS set of the target, the map kills
that subgroup. This makes explicit the exact target hypothesis needed by
model descent; constructing an NSS Lie neighbourhood remains separate. -/
theorem kills_subgroup_of_nss_image (f : LocalGroupHom W.restricted M)
    {V : Set H} (hV : M.IsNSS V) (hNV : ∀ h : S, h.val ∈ N → f.toFun h ∈ V) :
    ∀ h : S, h.val ∈ N → f.toFun h = M.one := by
  have hN : W.restricted.IsGlobalSubgroup (Subtype.val ⁻¹' N) := by
    refine ⟨W.subgroup.one_mem,?_,?_⟩
    · intro a ha
      exact W.subgroup.inv_mem a.val ha
    · intro a ha b hb
      obtain ⟨c,hc,hm⟩ := W.subgroup.mul_total a.val ha b.val hb
      exact ⟨⟨c,W.subset hc⟩,hc,hm⟩
  have himage := hN.image f
  have hsub : f.toFun '' (Subtype.val ⁻¹' N) ⊆ V := by
    rintro x ⟨h,hh,rfl⟩
    exact hNV h hh
  intro h hh
  exact hV _ himage hsub ⟨h,hh,rfl⟩
end NormalSubgroupWindow
end LocalGroupAlgebra
end DirectedCycles
