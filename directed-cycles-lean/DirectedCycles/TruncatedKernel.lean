import DirectedCycles.GroupRingKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false
open scoped MonoidAlgebra
namespace DirectedCycles

/-- The kernel after truncation is the image of the original group-ring
kernel; the ideal-power surjectivity is proved, not assumed. -/
theorem truncatedMap_kernel_image {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (D : ℕ) :
    (truncatedMap f D).toAddMonoidHom.ker =
      ((groupRingMap f).toAddMonoidHom.ker).map (truncate G D).toAddMonoidHom := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change truncate Q D (groupRingMap f a) = 0 at hx
    have ha := (Ideal.Quotient.eq_zero_iff_mem).mp hx
    obtain ⟨b,hb,he⟩ := groupRingMap_augmentation_power_surjective f hf D _ ha
    refine ⟨a-b,?_,?_⟩
    · change groupRingMap f (a-b) = 0
      rw [map_sub,he,sub_self]
    · change truncate G D (a-b) = truncate G D a
      rw [map_sub,(Ideal.Quotient.eq_zero_iff_mem).mpr hb,sub_zero]
  · rintro x ⟨a,ha,rfl⟩
    change truncate Q D (groupRingMap f a) = 0
    change groupRingMap f a = 0 at ha
    rw [ha,map_zero]

/-- The subgroup denoted I_K A: sums of kernel-element differences acting
on arbitrary elements of the truncated ring. -/
noncomputable def truncatedKernelRelations {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (D : ℕ) : AddSubgroup (TruncatedGroupRing G D) :=
  AddSubgroup.closure {y | ∃ k ∈ f.ker, ∃ x : TruncatedGroupRing G D,
    (truncatedElement G D k - 1) * x = y}

/-- The exact kernel needed by the spanning-through-fibres argument. -/
theorem truncatedMap_kernel {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (D : ℕ) :
    (truncatedMap f D).toAddMonoidHom.ker = truncatedKernelRelations f D := by
  let W := truncatedKernelRelations f D
  apply le_antisymm
  · have hle : (groupRingMap f).toAddMonoidHom.ker ≤ W.comap (truncate G D).toAddMonoidHom := by
      rw [groupRingMap_kernel_differences f hf]
      apply (W.comap (truncate G D).toAddMonoidHom).closure_le.mpr
      rintro y ⟨k,hk,g,rfl⟩
      change truncate G D ((MonoidAlgebra.of ℤ G k - 1) * MonoidAlgebra.of ℤ G g) ∈ W
      rw [map_mul,map_sub,map_one]
      exact AddSubgroup.subset_closure ⟨k,hk,truncatedElement G D g,rfl⟩
    rw [truncatedMap_kernel_image f hf D]
    rintro x ⟨a,ha,rfl⟩
    exact hle ha
  · apply ((truncatedMap f D).toAddMonoidHom.ker).closure_le.mpr
    rintro y ⟨k,hk,x,rfl⟩
    change f k = 1 at hk
    change truncatedMap f D ((truncatedElement G D k - 1) * x) = 0
    rw [map_mul,map_sub,map_one,truncatedMap_element,hk,map_one,sub_self,zero_mul]

/-- The additive quotient A/(I_K A) is canonically the truncated group ring
of the quotient group (and more generally of any surjective image). -/
noncomputable def truncatedQuotientEquiv {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (D : ℕ) :
    TruncatedGroupRing G D ⧸ truncatedKernelRelations f D ≃+ TruncatedGroupRing Q D :=
  (QuotientAddGroup.quotientAddEquivOfEq (truncatedMap_kernel f hf D).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (truncatedMap f D).toAddMonoidHom
      (truncatedMap_surjective f hf D))

end DirectedCycles
