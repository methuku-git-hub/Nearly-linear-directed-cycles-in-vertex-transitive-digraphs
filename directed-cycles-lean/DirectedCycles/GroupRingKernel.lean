module

public import DirectedCycles.TruncatedFunctor

@[expose] public section

set_option autoImplicit false
open scoped MonoidAlgebra
namespace DirectedCycles

/-- The additive relations identifying basis elements with the same image. -/
noncomputable def groupRingRelations {G Q : Type*} [Group G] [Group Q] (f : G →* Q) : AddSubgroup ℤ[G] :=
  AddSubgroup.closure {x | ∃ g h : G, f g = f h ∧ MonoidAlgebra.of ℤ G g - MonoidAlgebra.of ℤ G h = x}

/-- Any surjective map of group rings has exactly the expected additive
kernel. A set-theoretic section is used only to prove this identity. -/
theorem groupRingMap_kernel {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) :
    (groupRingMap f).toAddMonoidHom.ker = groupRingRelations f := by
  classical
  let s : Q → G := Function.surjInv hf
  let l : ℤ[Q] →+ ℤ[G] := MonoidAlgebra.liftNC (Int.castRingHom ℤ[G]).toAddMonoidHom
    (fun q => MonoidAlgebra.of ℤ G (s q))
  have hl (q : Q) : l (MonoidAlgebra.of ℤ Q q) = MonoidAlgebra.of ℤ G (s q) := by
    simp [l,MonoidAlgebra.of_apply]
  have hres : ∀ x : ℤ[G], x - l (groupRingMap f x) ∈ groupRingRelations f := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      rw [groupRingMap_of,hl]
      exact AddSubgroup.subset_closure ⟨g,s (f g),(Function.surjInv_eq hf (f g)).symm,rfl⟩
    | add x y hx hy =>
      rw [map_add,map_add]
      have he : x+y-(l (groupRingMap f x)+l (groupRingMap f y)) =
        (x-l (groupRingMap f x))+(y-l (groupRingMap f y)) := by abel
      rw [he]
      exact AddSubgroup.add_mem _ hx hy
    | smul z x hx =>
      rw [map_zsmul,map_zsmul,← smul_sub]
      exact AddSubgroup.zsmul_mem _ hx z
  apply le_antisymm
  · intro x hx
    change groupRingMap f x = 0 at hx
    simpa only [hx,map_zero,sub_zero] using hres x
  · apply ((groupRingMap f).toAddMonoidHom.ker).closure_le.mpr
    rintro x ⟨g,h,he,rfl⟩
    change groupRingMap f (MonoidAlgebra.of ℤ G g - MonoidAlgebra.of ℤ G h) = 0
    rw [map_sub,groupRingMap_of,groupRingMap_of,he,sub_self]

/-- The same kernel expressed using differences from the kernel subgroup. -/
theorem groupRingMap_kernel_differences {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) :
    (groupRingMap f).toAddMonoidHom.ker =
      AddSubgroup.closure {x | ∃ k ∈ f.ker, ∃ g : G,
        (MonoidAlgebra.of ℤ G k - 1) * MonoidAlgebra.of ℤ G g = x} := by
  let W := AddSubgroup.closure {x | ∃ k ∈ f.ker, ∃ g : G,
        (MonoidAlgebra.of ℤ G k - 1) * MonoidAlgebra.of ℤ G g = x}
  apply le_antisymm
  · rw [groupRingMap_kernel f hf]
    apply W.closure_le.mpr
    rintro x ⟨g,h,he,rfl⟩
    have hk : g*h⁻¹ ∈ f.ker := by change f (g*h⁻¹) = 1; rw [map_mul,map_inv,he,mul_inv_cancel]
    have hid : (MonoidAlgebra.of ℤ G (g*h⁻¹)-1) * MonoidAlgebra.of ℤ G h =
        MonoidAlgebra.of ℤ G g - MonoidAlgebra.of ℤ G h := by
      rw [sub_mul,one_mul,← map_mul,inv_mul_cancel_right]
    exact AddSubgroup.subset_closure ⟨g*h⁻¹,hk,h,hid⟩
  · apply ((groupRingMap f).toAddMonoidHom.ker).closure_le.mpr
    rintro x ⟨k,hk,g,rfl⟩
    change f k = 1 at hk
    change groupRingMap f ((MonoidAlgebra.of ℤ G k - 1) * MonoidAlgebra.of ℤ G g) = 0
    rw [map_mul,map_sub,map_one,groupRingMap_of,hk,map_one,sub_self,zero_mul]

/-- Surjective ring maps with surjective ideal restriction lift every power
of the ideal, without a commutativity hypothesis. -/
theorem ringHom_ideal_power_surjective {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) (I : Ideal R) (J : Ideal S)
    (h : ∀ y ∈ J, ∃ x ∈ I, f x = y) (n : ℕ) :
    ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, f x = y := by
  induction n with
  | zero =>
    intro y _
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨x,by rw [Submodule.pow_zero,Ideal.one_eq_top]; exact Submodule.mem_top,rfl⟩
  | succ n ih =>
    intro y hy
    rw [Submodule.pow_succ] at hy ⊢
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨x,hx,rfl⟩ := ih a ha
      obtain ⟨z,hz,rfl⟩ := h b hb
      exact ⟨x*z,Ideal.mul_mem_mul hx hz,map_mul f x z⟩
    · intro a b ha hb
      obtain ⟨x,hx,rfl⟩ := ha
      obtain ⟨z,hz,rfl⟩ := hb
      exact ⟨x+z,Submodule.add_mem _ hx hz,map_add f x z⟩

theorem groupRingMap_augmentation_power_surjective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (D : ℕ) :
    ∀ y ∈ augmentationIdeal Q ^ D,
      ∃ x ∈ augmentationIdeal G ^ D, groupRingMap f x = y := by
  apply ringHom_ideal_power_surjective (groupRingMap f) (groupRingMap_surjective f hf)
  intro y hy
  obtain ⟨x,rfl⟩ := groupRingMap_surjective f hf y
  refine ⟨x,?_,rfl⟩
  change augmentation G x = 0
  rw [← augmentation_groupRingMap f x]
  exact hy

end DirectedCycles
