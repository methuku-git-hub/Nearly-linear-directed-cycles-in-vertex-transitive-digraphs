import DirectedCycles.TruncatedKernel
import DirectedCycles.OperatorSpans
import DirectedCycles.TruncatedPowers

set_option autoImplicit false
namespace DirectedCycles

/-- Differences from the kernel act by left multiplication. -/
noncomputable def kernelDifferenceOperator {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (D : ℕ) (k : f.ker) : Module.End ℤ (TruncatedGroupRing G D) :=
  LinearMap.mulLeft ℤ (truncatedElement G D k.val - 1)

/-- All D-fold products of these actual operators vanish. -/
theorem kernelDifferenceOperator_product {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (D : ℕ) (s : Fin D → f.ker) :
    (List.ofFn (fun i => kernelDifferenceOperator f D (s i))).prod = 0 := by
  have hprod : ∀ ks : List f.ker, ∀ x : TruncatedGroupRing G D,
      ((ks.map (kernelDifferenceOperator f D)).prod) x =
        (ks.map (fun k => truncatedElement G D k.val - 1)).prod * x := by
    intro ks
    induction ks with
    | nil => intro x; simp
    | cons k ks ih =>
      intro x
      simp only [List.map_cons,List.prod_cons,Module.End.mul_apply,ih]
      change (truncatedElement G D k.val - 1) *
        ((ks.map (fun k => truncatedElement G D k.val - 1)).prod*x) = _
      exact (mul_assoc _ _ _).symm
  have hz := truncated_difference_product D (List.ofFn (fun i => (s i).val)) (by simp)
  apply LinearMap.ext
  intro x
  have hp := hprod (List.ofFn s) x
  simp only [List.map_ofFn,Function.comp_def] at hp hz
  rw [hp,hz,zero_mul]
  rfl

/-- An additive subgroup that is stable under the kernel and spans the
quotient already spans the full truncated group ring. -/
theorem truncated_spanning_descent {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (D : ℕ)
    (W : AddSubgroup (TruncatedGroupRing G D))
    (hstable : ∀ k ∈ f.ker, ∀ x ∈ W, truncatedElement G D k * x ∈ W)
    (hspan : W.map (truncatedMap f D).toAddMonoidHom = ⊤) : W = ⊤ := by
  let I := Submodule.span ℤ (Set.range (kernelDifferenceOperator f D))
  have hnil : I ^ D = ⊥ := operator_span_nilpotent (kernelDifferenceOperator f D) D
    (kernelDifferenceOperator_product f D)
  have hIW : I • W.toIntSubmodule ≤ W.toIntSubmodule := by
    apply operator_span_stable
    intro k x hx
    change (truncatedElement G D k.val - 1)*x ∈ W
    rw [sub_mul,one_mul]
    exact W.sub_mem (hstable k.val k.property x hx) hx
  have hker : (truncatedMap f D).toAddMonoidHom.ker ≤
      (I • (⊤ : Submodule ℤ (TruncatedGroupRing G D))).toAddSubgroup := by
    rw [truncatedMap_kernel f hf D]
    apply ((I • (⊤ : Submodule ℤ (TruncatedGroupRing G D))).toAddSubgroup).closure_le.mpr
    rintro y ⟨k,hk,x,rfl⟩
    have ht : kernelDifferenceOperator f D ⟨k,hk⟩ ∈ I := Submodule.subset_span ⟨⟨k,hk⟩,rfl⟩
    exact Submodule.smul_mem_smul ht (Submodule.mem_top (x := x))
  have hsup : W.toIntSubmodule ⊔ I • (⊤ : Submodule ℤ (TruncatedGroupRing G D)) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : truncatedMap f D x ∈ W.map (truncatedMap f D).toAddMonoidHom := by rw [hspan]; trivial
    obtain ⟨w,hw,he⟩ := hx
    change truncatedMap f D w = truncatedMap f D x at he
    have hk : x-w ∈ (truncatedMap f D).toAddMonoidHom.ker := by
      change truncatedMap f D (x-w) = 0
      rw [map_sub,he,sub_self]
    have hwi : w ∈ W.toIntSubmodule := hw
    have hxi : x-w ∈ I • (⊤ : Submodule ℤ (TruncatedGroupRing G D)) := hker hk
    have hm := Submodule.add_mem_sup hwi hxi
    convert hm using 1
    abel
  have hout := nilpotent_operator_spanning I W.toIntSubmodule D hIW hsup
    (by rw [hnil,Submodule.bot_smul])
  exact congrArg Submodule.toAddSubgroup hout

end DirectedCycles
