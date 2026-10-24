import DirectedCycles.Augmentation
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Group.Subgroup.Map

set_option autoImplicit false
open scoped MonoidAlgebra
namespace DirectedCycles

/-- A cocycle for an integral representation. Only this elementary identity
is used; no group-cohomology theorem is assumed. -/
def IsAdditiveCocycle {G A : Type*} [Group G] [AddCommGroup A]
    (T : G →* Module.End ℤ A) (f : G → A) : Prop :=
  ∀ g h, f (g*h) = f g + T g (f h)

/-- The unique additive extension of a map on group elements. -/
noncomputable def groupRingAdditiveExtension {G A : Type*} [Group G] [AddCommGroup A]
    (f : G → A) : ℤ[G] →+ A :=
  (Finsupp.liftAddHom (fun g =>
    { toFun := fun z : ℤ => z • f g
      map_zero' := zero_zsmul _
      map_add' := fun z w => add_zsmul _ z w })).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] theorem groupRingAdditiveExtension_of {G A : Type*} [Group G] [AddCommGroup A]
    (f : G → A) (g : G) :
    groupRingAdditiveExtension f (MonoidAlgebra.of ℤ G g) = f g := by
  simp [groupRingAdditiveExtension,MonoidAlgebra.of_apply]

theorem cocycle_one {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f) : f 1 = 0 := by
  have h := hf 1 1
  simp only [one_mul,map_one,Module.End.one_apply] at h
  exact add_left_cancel (show f 1 + f 1 = f 1 + 0 by simpa using h.symm)

/-- Left translation of a group-ring argument under the additive cocycle extension. -/
theorem cocycle_extension_left_mul {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f)
    (g : G) (x : ℤ[G]) :
    groupRingAdditiveExtension f (MonoidAlgebra.of ℤ G g * x) =
      augmentation G x • f g + T g (groupRingAdditiveExtension f x) := by
  induction x using MonoidAlgebra.induction_on with
  | of h =>
    rw [← map_mul,groupRingAdditiveExtension_of,augmentation_of,one_zsmul,groupRingAdditiveExtension_of]
    exact hf g h
  | add x y hx hy =>
    rw [mul_add,map_add,map_add,map_add,add_zsmul,map_add,hx,hy]
    abel
  | smul z x hx =>
    rw [mul_smul_comm,map_zsmul,map_zsmul,map_zsmul,map_zsmul,hx,smul_add]
    simp only [smul_smul,smul_eq_mul]

/-- On zero-augmentation arguments, multiplication by g-1 corresponds
exactly to applying the operator T_g-I. -/
theorem cocycle_extension_difference {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f)
    (g : G) (x : ℤ[G]) (hx : augmentation G x = 0) :
    groupRingAdditiveExtension f ((MonoidAlgebra.of ℤ G g-1)*x) =
      (T g-1) (groupRingAdditiveExtension f x) := by
  rw [sub_mul,one_mul,map_sub,cocycle_extension_left_mul hf,hx,zero_zsmul,zero_add]
  rfl

end DirectedCycles
