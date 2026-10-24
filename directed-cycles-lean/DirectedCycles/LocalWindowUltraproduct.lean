import DirectedCycles.LocalInternalImages
import DirectedCycles.LocalGroupHom

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (S : ∀ i, Set (G i)) (h1 : ∀ i, (L i).one ∈ S i) (hi : ∀ i, ∀ x ∈ S i, (L i).inv x ∈ S i)

/-- Reduced products of arbitrary local windows map into the exact internal
window, without an ambient global group. -/
def localUltraWindowMap : LocalUltraproduct F (fun i => S i) → localUltraSet F G S :=
  Quotient.lift (fun a => ⟨localUltraMk F G (fun i => (a i).val),
    (localUltraMk_mem_iff F G S _).2 (Filter.Eventually.of_forall fun i => (a i).property)⟩) (by
      intro a b hab
      apply Subtype.ext
      exact Quotient.sound (hab.mono fun _ h => congrArg Subtype.val h))

theorem localUltraWindowMap_injective : Function.Injective (localUltraWindowMap F G S) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b he
  apply Quotient.sound
  have hv := congrArg Subtype.val he
  have hh := (localUltraMk_eq_iff F G (fun i => (a i).val) (fun i => (b i).val)).1 hv
  exact hh.mono fun _ h => Subtype.ext h

include h1 in
theorem localUltraWindowMap_surjective : Function.Surjective (localUltraWindowMap F G S) := by
  classical
  intro x
  obtain ⟨v,hv⟩ := Quotient.exists_rep x.val
  have hv' : localUltraMk F G v = x.val := hv
  have hvS : ∀ᶠ i in F, v i ∈ S i := (localUltraMk_mem_iff F G S v).1 (by rw [hv']; exact x.property)
  let a : ∀ i, S i := fun i => if h : v i ∈ S i then ⟨v i,h⟩ else ⟨(L i).one,h1 i⟩
  refine ⟨localUltraMk F (fun i => S i) a,?_⟩
  apply Subtype.ext
  change localUltraMk F G (fun i => (a i).val) = x.val
  rw [← hv]
  apply Quotient.sound
  filter_upwards [hvS] with i h
  dsimp only [a]
  rw [dite_eq_left h]

noncomputable def localUltraWindowEquiv : LocalUltraproduct F (fun i => S i) ≃ localUltraSet F G S :=
  Equiv.ofBijective (localUltraWindowMap F G S)
    ⟨localUltraWindowMap_injective F G S,localUltraWindowMap_surjective F G L S h1⟩

include h1 in
theorem localUltraWindow_one_mem : (localUltraAlgebra F G L).one ∈ localUltraSet F G S :=
  (localUltraMk_mem_iff F G S _).2 (Filter.Eventually.of_forall h1)

include hi in
theorem localUltraWindow_inv_mem : ∀ x ∈ localUltraSet F G S,
    (localUltraAlgebra F G L).inv x ∈ localUltraSet F G S := by
  rintro x ⟨a,ha,rfl⟩
  exact (localUltraMk_mem_iff F G S _).2 (ha.mono fun i hai => hi i (a i) hai)

abbrev localUltraWindowAlgebra := (localUltraAlgebra F G L).restrict (localUltraSet F G S)
  (localUltraWindow_one_mem F G L S h1) (localUltraWindow_inv_mem F G L S hi)

/-- Restriction commutes with the actual local ultraproduct, including exact
multiplication domains. -/
theorem localUltraWindowEquiv_mul_iff (x y z : LocalUltraproduct F (fun i => S i)) :
    (localUltraAlgebra F (fun i => S i) (fun i => (L i).restrict (S i) (h1 i) (hi i))).mulRel x y z ↔
      (localUltraWindowAlgebra F G L S h1 hi).mulRel
        (localUltraWindowEquiv F G L S h1 x) (localUltraWindowEquiv F G L S h1 y)
        (localUltraWindowEquiv F G L S h1 z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  change (localUltraAlgebra F (fun i => S i) (fun i => (L i).restrict (S i) (h1 i) (hi i))).mulRel
      (localUltraMk F _ a) (localUltraMk F _ b) (localUltraMk F _ c) ↔
    (localUltraAlgebra F G L).mulRel (localUltraMk F G (fun i => (a i).val))
      (localUltraMk F G (fun i => (b i).val)) (localUltraMk F G (fun i => (c i).val))
  exact (localUltraMulRel_mk_iff F (fun i => S i)
    (fun i => (L i).restrict (S i) (h1 i) (hi i)) a b c).trans
      (localUltraMulRel_mk_iff F G L (fun i => (a i).val) (fun i => (b i).val) (fun i => (c i).val)).symm
end DirectedCycles
