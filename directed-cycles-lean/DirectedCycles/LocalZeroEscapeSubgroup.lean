module

public import DirectedCycles.LocalGlobalSubgroup
public import DirectedCycles.LocalEscapeMaps
public import DirectedCycles.LocalWordPowers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The identity has every all-bracketings power defined, even in a local
ambient group. -/
theorem product_replicate_one (n : ℕ) : L.Product (List.replicate n L.one) L.one := by
  let f : LocalGroupHom (ofGroup (Multiplicative ℤ)) L := {
    toFun := fun _ => L.one
    map_one := rfl
    map_inv := fun _ => L.inv_one.symm
    map_mul := fun _ => L.one_mul L.one }
  have h := (ofGroup_product (Multiplicative ℤ) (List.replicate n 1)).map f
  simpa only [List.map_replicate] using h

theorem escapeNorm_one {A : Set G} (hA : L.one ∈ A) : L.escapeNorm A L.one = 0 :=
  (L.escapeNorm_eq_zero_iff hA L.one).2 (fun n => ⟨L.one,hA,L.product_replicate_one n⟩)

/-- The exact zero-escape set is a genuine global subgroup once the binary
Gleason estimate is established. Total multiplication on this set is proved
from the two-letter domain, not assumed for the whole local group. -/
theorem zero_escape_isGlobalSubgroup (hL : L.Reversible) {A : Set G}
    (hA : L.one ∈ A) (hi : ∀ x ∈ A, L.inv x ∈ A)
    (hdom : L.AllProductsDefined A 2) (C : ℝ)
    (hprod : ∀ x ∈ A, ∀ y ∈ A, ∀ z, L.mulRel x y z →
      L.escapeNorm A z ≤ C*(L.escapeNorm A x+L.escapeNorm A y)) :
    L.IsGlobalSubgroup {x | L.escapeNorm A x = 0} := by
  refine ⟨L.escapeNorm_one hA,?_,?_⟩
  · intro x hx
    change L.escapeNorm A (L.inv x) = 0
    rw [L.escapeNorm_inv hL hi]
    exact hx
  · intro x hx y hy
    change L.escapeNorm A x = 0 at hx
    change L.escapeNorm A y = 0 at hy
    have hxA : x ∈ A := L.mem_of_escapeNorm_lt_one hA (by rw [hx]; norm_num)
    have hyA : y ∈ A := L.mem_of_escapeNorm_lt_one hA (by rw [hy]; norm_num)
    obtain ⟨z,hz⟩ := hdom [x,y] (by simp) (by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hxA
      · have he := List.mem_singleton.mp ha
        exact he ▸ hyA)
    obtain ⟨a,b,ha,hb,hm⟩ := hz.split L (a := [x]) (b := [y]) rfl (by simp) (by simp)
    have he : a = x := (Product.singleton_iff L).1 ha
    have he' : b = y := (Product.singleton_iff L).1 hb
    rw [he,he'] at hm
    have hbound := hprod x hxA y hyA z hm
    have hz0 : L.escapeNorm A z = 0 := by
      apply le_antisymm _ (L.escapeNorm_nonneg hA z)
      simpa only [hx,hy,add_zero,mul_zero] using hbound
    exact ⟨z,hz0,hm⟩

/-- Every defined conjugate of a zero-escape element again has zero escape
under the stated conjugation estimate. -/
theorem conjugate_zero_escape {A : Set G} (hA : L.one ∈ A)
    {g x z : G} (hx : L.escapeNorm A x = 0) {C : ℝ}
    (hbound : L.escapeNorm A z ≤ C*L.escapeNorm A x)
    (_hconj : L.Product [L.inv g,x,g] z) : L.escapeNorm A z = 0 := by
  apply le_antisymm _ (L.escapeNorm_nonneg hA z)
  simpa only [hx,mul_zero] using hbound
end LocalGroupAlgebra
end DirectedCycles
