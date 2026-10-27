module

public import DirectedCycles.LocalZeroEscapeSubgroup
public import DirectedCycles.LocalNormalThickening
public import DirectedCycles.LocalSubgroupConjugation
public import DirectedCycles.LocalSubgroupTransport
public import DirectedCycles.LocalWindowNSS

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Trapping complete subgroup powers in the third word power forces every
such subgroup into A. -/
theorem subgroup_subset_of_power_trapping {A T : Set G} {m : ℕ}
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ m → L.PowerIn (L.wordPower A 3) x j) → x ∈ A)
    (hT : L.IsGlobalSubgroup T) (hTA : T ⊆ L.wordPower A 3) : T ⊆ A := by
  intro x hx
  apply htrap
  intro j _ _
  obtain ⟨y,hy,hp⟩ := hT.powerIn hx j
  exact ⟨y,hTA hy,hp⟩

/-- In a local ambient group, the product estimate and first trapping property
suffice to construct the normal zero-escape subgroup and its actual NSS local
quotient. Normality is proved by conjugating the subgroup with six-letter
products; it is not supplied as an extra premise. -/
theorem zero_escape_normal_window_nss
    (hd : L.DivisionClosed) (hr : L.Reversible) {A : Set G}
    (hA : L.one ∈ A) (hi : ∀ x ∈ A, L.inv x ∈ A)
    (hdom : L.AllProductsDefined A 6) (C : ℝ)
    (hprod : ∀ x ∈ A, ∀ y ∈ A, ∀ z, L.mulRel x y z →
      L.escapeNorm A z ≤ C*(L.escapeNorm A x+L.escapeNorm A y))
    (m : ℕ)
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ m → L.PowerIn (L.wordPower A 3) x j) → x ∈ A) :
    let H := {x | L.escapeNorm A x = 0}
    ∃ W : L.NormalSubgroupWindow H (L.setMul H A),
      (W.congruence hd hr).algebra.IsNSS Set.univ := by
  dsimp only
  let H : Set G := {x | L.escapeNorm A x = 0}
  have hH : L.IsGlobalSubgroup H := L.zero_escape_isGlobalSubgroup hr hA hi
    (hdom.mono L (Set.Subset.refl A) (by omega : 2 ≤ 6)) C hprod
  have hHA : H ⊆ A := by
    intro x hx
    apply L.mem_of_escapeNorm_lt_one hA
    change L.escapeNorm A x = 0 at hx
    rw [hx]
    norm_num
  have hnorm : ∀ b ∈ A, ∀ h ∈ H, ∃ k ∈ H, ∃ t, L.mulRel b h t ∧ L.mulRel k b t := by
    intro b hb h hh
    let := hH.toGroup
    obtain ⟨f,hf⟩ := hH.exists_conjugationHom hr hHA hdom hb (hi b hb)
    have hall : (ofGroup H).IsGlobalSubgroup Set.univ :=
      ⟨Set.mem_univ _,fun _ _ => Set.mem_univ _,fun x _ y _ => ⟨x*y,Set.mem_univ _,rfl⟩⟩
    have hT := hall.image f
    have hT3 : f.toFun '' Set.univ ⊆ L.wordPower A 3 := by
      rintro x ⟨a,_,rfl⟩
      refine ⟨[b,a.val,L.inv b],rfl,?_,hf a⟩
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact hb
      · exact hHA a.property
      · exact hi b hb
    have hTA := L.subgroup_subset_of_power_trapping htrap hT hT3
    let h' : H := ⟨h,hh⟩
    have hkh : f.toFun h' ∈ H := hT.escapeNorm_eq_zero hTA hA ⟨h',Set.mem_univ _,rfl⟩
    obtain ⟨u,v,hu,hv,hm⟩ := (hf h').split L (a := [b,h]) (b := [L.inv b]) rfl (by simp) (by simp)
    have hev : v = L.inv b := (Product.singleton_iff L).1 hv
    have hu' : L.mulRel b h u := (Product.pair_iff L _ _ _).1 hu
    have hconj : L.mulRel u (L.inv b) (f.toFun h') := by simpa only [hev] using hm
    have hswitch : L.mulRel (f.toFun h') b u := by simpa only [L.inv_inv] using hd.right hconj
    exact ⟨f.toFun h',hkh,u,hu',hswitch⟩
  let W := hH.normalThickening hr hHA (Set.Subset.refl A) hA hi
    (hdom.mono L (Set.Subset.refl A) (by omega : 4 ≤ 6)) hnorm
  refine ⟨W,W.zero_escape_quotient_isNSS hd hr hA rfl ?_⟩
  intro T hT hTS
  apply L.subgroup_subset_of_power_trapping htrap hT
  intro x hx
  obtain ⟨h,hh,a,ha,hm⟩ := hTS hx
  have hx2 : x ∈ L.wordPower A 2 :=
    ⟨[h,a],rfl,by simpa only [List.mem_cons,List.not_mem_nil,or_false] using
      (show ∀ y, y = h ∨ y = a → y ∈ A from fun y hy => by rcases hy with rfl | rfl; exact hHA hh; exact ha),
      (Product.pair_iff L _ _ _).2 hm⟩
  rw [show 3 = 2+1 by rfl,L.wordPower_add hdom (by omega : 2+1 ≤ 6),L.wordPower_one]
  exact ⟨x,hx2,L.one,hA,L.mul_one x⟩
end LocalGroupAlgebra
end DirectedCycles
