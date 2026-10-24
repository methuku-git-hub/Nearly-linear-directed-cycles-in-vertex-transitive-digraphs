import DirectedCycles.GlobalWindowPowerLifting
import DirectedCycles.LocalGlobalApproximateConversion
import DirectedCycles.StrongLocalApproximateGroups
import DirectedCycles.StrongApproximateGroups

set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped Pointwise
namespace DirectedCycles

/-- A strong approximate group in an actual ambient-group window is
globally strong. All trapping powers and conjugate words are lifted through
the window before applying the local hypotheses. -/
theorem strong_global_window_transfer {G : Type*} [Group G] [DecidableEq G]
    (W : Set G) (h1 : (1 : G) ∈ W) (hi : ∀ x ∈ W, x⁻¹ ∈ W)
    {K : ℕ} {A : Finset W}
    (hA : IsStrongLocalFiniteApproximateGroup ((LocalGroupAlgebra.ofGroup G).restrict W h1 hi) K A) :
    IsStrongFiniteApproximateGroup K (A.image Subtype.val) := by
  classical
  let L := (LocalGroupAlgebra.ofGroup G).restrict W h1 hi
  let f := LocalGroupHom.inclusion (LocalGroupAlgebra.ofGroup G) W h1 hi
  let B := A.image Subtype.val
  have hBimage : (B : Set G) = f.toFun '' (A : Set W) := Finset.coe_image
  have hpowers : ∀ m ≤ 200, Subtype.val '' L.wordPower (A : Set W) m = (B : Set G)^m := by
    intro m hm
    simpa only [LocalGroupAlgebra.ofGroup_wordPower,B,Finset.coe_image,f,L,LocalGroupHom.inclusion] using
      LocalGroupAlgebra.wordPower_image f hA.approximate.allProducts hm
  have hB : IsApproximateSubgroup (K : ℝ) (B : Set G) := by
    simpa only [f,LocalGroupHom.inclusion] using local_global_approximate_conversion (hA.approximate.image f)
  obtain ⟨S,hSi,hQdom,hsmall,hfirst,hsecond⟩ := hA.trapping
  have hS1 : L.one ∈ S := hsecond L.one
    (fun j _ _ => ⟨L.one,hA.approximate.one_mem,L.product_replicate_one j⟩)
  have hA41 : L.one ∈ L.wordPower (A : Set W) 4 :=
    ⟨List.replicate 4 L.one,List.length_replicate,by
      intro x hx
      exact (List.mem_replicate.mp hx).2.symm ▸ hA.approximate.one_mem,L.product_replicate_one 4⟩
  have hSQ : S ⊆ L.conjugates S (L.wordPower (A : Set W) 4) := L.subset_conjugates hA41
  have hQ1 := hSQ hS1
  have hK0 : 0 < K := by have := hA.approximate.one_le; omega
  have hSA : S ⊆ A := hSQ.trans (by
    simpa only [L.wordPower_one] using L.wordPower_subset_of_maximum hQ1 hQdom hsmall
      1 (Nat.succ_le_of_lt (Nat.mul_pos (by omega) (pow_pos hK0 3))))
  have hconj : Subtype.val '' L.conjugates S (L.wordPower (A : Set W) 4) =
      setConjugates (Subtype.val '' S) ((B : Set G)^4) := by
    apply Set.Subset.antisymm
    · rintro x ⟨z,⟨s,hs,b,hb,hp⟩,rfl⟩
      refine ⟨s.val,⟨s,hs,rfl⟩,b.val,?_,?_⟩
      · rw [← hpowers 4 (by omega)]
        exact ⟨b,hb,rfl⟩
      · have hh := (LocalGroupAlgebra.ofGroup_product_iff G _ _).1 (hp.map f)
        simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
          f,L,LocalGroupHom.inclusion,LocalGroupAlgebra.restrict,LocalGroupAlgebra.ofGroup,mul_assoc] using hh
    · rintro x ⟨s,⟨s',hs,rfl⟩,b,hb,rfl⟩
      rw [← hpowers 4 (by omega)] at hb
      obtain ⟨b',hb',rfl⟩ := hb
      have hs4 : s' ∈ L.wordPower (A : Set W) 4 := by
        apply L.wordPower_subset_wordPower hA.approximate.one_mem hA.approximate.allProducts
          (by omega : 1 ≤ 4) (by omega)
        simpa only [L.wordPower_one] using hSA hs
      have hrev : (LocalGroupAlgebra.ofGroup G).Reversible := LocalGroupAlgebra.ofGroup_reversible G
      have hbi := L.inv_mem_wordPower (hrev.restrict (LocalGroupAlgebra.ofGroup G) W h1 hi)
        hA.approximate.inv_mem hb'
      obtain ⟨z,hz⟩ := (hA.approximate.allProducts.wordPower L (by omega : 4*3 ≤ 200))
        [L.inv b',s',b'] (by simp) (by
          intro y hy
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
          rcases hy with rfl | rfl | rfl
          · exact hbi
          · exact hs4
          · exact hb')
      refine ⟨z,⟨s',hs,b',hb',hz⟩,?_⟩
      have hh := (LocalGroupAlgebra.ofGroup_product_iff G _ _).1 (hz.map f)
      simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
          f,L,LocalGroupHom.inclusion,LocalGroupAlgebra.restrict,LocalGroupAlgebra.ofGroup,mul_assoc] using hh
  refine ⟨hA.approximate.one_le,hB,Subtype.val '' S,?_,?_,?_,?_⟩
  · ext x
    change x⁻¹ ∈ Subtype.val '' S ↔ x ∈ Subtype.val '' S
    constructor
    · rintro ⟨s,hs,he⟩
      refine ⟨L.inv s,hSi s hs,?_⟩
      change s.val⁻¹ = x
      rw [he,inv_inv]
    · rintro ⟨s,hs,rfl⟩
      exact ⟨L.inv s,hSi s hs,rfl⟩
  · rw [← hconj]
    have he := LocalGroupAlgebra.wordPower_image f hQdom (le_refl (1000*K^3))
    simp only [LocalGroupAlgebra.ofGroup_wordPower,f,LocalGroupHom.inclusion] at he
    change Subtype.val '' L.wordPower (L.conjugates S (L.wordPower (A : Set W) 4)) (1000*K^3) =
      (Subtype.val '' L.conjugates S (L.wordPower (A : Set W) 4))^(1000*K^3) at he
    rw [← he]
    rintro x ⟨y,hy,rfl⟩
    exact Finset.mem_image.mpr ⟨y,hsmall hy,rfl⟩
  · intro x hx
    have hx1 := hx 1 (by omega) (by omega)
    rw [pow_one,← hpowers 100 (by omega)] at hx1
    obtain ⟨x',_hx',rfl⟩ := hx1
    apply Finset.mem_image.mpr
    refine ⟨x',hfirst x' ?_,rfl⟩
    intro j hj hjmax
    apply LocalGroupAlgebra.restricted_powerIn_of_powers W h1 hi
    intro k hk
    rw [hpowers 100 (by omega)]
    by_cases hk0 : k = 0
    · subst k
      exact pow_zero x'.val ▸ Set.one_mem_pow hB.one_mem
    · exact hx k (by omega) (by omega)
  · intro x hx
    have hx1 := hx 1 (by omega) (Nat.succ_le_of_lt (Nat.mul_pos (by omega) (pow_pos hK0 3)))
    rw [pow_one] at hx1
    obtain ⟨x',_hx',rfl⟩ := Finset.mem_image.mp hx1
    refine ⟨x',hsecond x' ?_,rfl⟩
    intro j hj hjmax
    apply LocalGroupAlgebra.restricted_powerIn_of_powers W h1 hi
    intro k hk
    change x'.val^k ∈ f.toFun '' (A : Set W)
    rw [← hBimage]
    by_cases hk0 : k = 0
    · subst k
      simpa only [pow_zero] using hB.one_mem
    · exact hx k (by omega) (by omega)
end DirectedCycles
