import DirectedCycles.LocalUltraproductMaps
import DirectedCycles.LocalUltraproductDomain
import Mathlib.Order.Filter.Ultrafilter.Basic

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (s : Set ι) (hs : s ∈ U)

/-- Restrict the index type to an actual ultrafilter-large set. -/
def localLargeIndexUltrafilter : Ultrafilter s :=
  U.comap Subtype.val_injective (by simpa only [Subtype.range_coe] using hs)

theorem localLargeIndex_eventually_iff (P : s → Prop) :
    (∀ᶠ j in (localLargeIndexUltrafilter U s hs : Filter s), P j) ↔
      ∀ᶠ i in (U : Filter ι), ∀ h : i ∈ s, P ⟨i,h⟩ := by
  change (∀ᶠ j in Filter.comap Subtype.val (U : Filter ι), P j) ↔ _
  rw [Filter.eventually_comap]
  constructor
  · intro h
    exact h.mono fun i hi hsi => hi ⟨i,hsi⟩ rfl
  · intro h
    exact h.mono fun _ hi j hj => by subst hj; exact hi j.property

theorem localLargeIndex_eventually (P : ι → Prop) :
    (∀ᶠ j in (localLargeIndexUltrafilter U s hs : Filter s), P j.val) ↔
      ∀ᶠ i in (U : Filter ι), P i := by
  rw [localLargeIndex_eventually_iff]
  constructor
  · intro h
    filter_upwards [h,hs] with i hi hsi
    exact hi hsi
  · exact fun h => h.mono fun _ hi _ => hi

variable (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Restrict actual representatives; equality and multiplication are
transported using the proved large-index equivalence. -/
def localLargeIndexRestrict : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L)
    (localUltraAlgebra (localLargeIndexUltrafilter U s hs : Filter s)
      (fun j => G j.val) (fun j => L j.val)) where
  toFun := Quotient.map (fun a j => a j.val) (by
    intro a b hab
    exact (localLargeIndex_eventually U s hs (fun i => a i = b i)).2 hab)
  map_one := rfl
  map_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h a => rfl
  map_mul := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c hm
    exact (localUltraMulRel_mk_iff _ _ _ _ _ _).2
      ((localLargeIndex_eventually U s hs _).2 ((localUltraMulRel_mk_iff _ _ _ a b c).1 hm))

/-- Extend representatives by the local identity outside the large set.
The values on those discarded indices play no role in the ultraproduct. -/
noncomputable def localLargeIndexExtend : LocalGroupHom
    (localUltraAlgebra (localLargeIndexUltrafilter U s hs : Filter s)
      (fun j => G j.val) (fun j => L j.val)) (localUltraAlgebra (U : Filter ι) G L) := by
  classical
  refine {
    toFun := Quotient.map (fun a i => if hi : i ∈ s then a ⟨i,hi⟩ else (L i).one) ?_
    map_one := ?_
    map_inv := ?_
    map_mul := ?_ }
  · intro a b hab
    have hh := (localLargeIndex_eventually_iff U s hs _).1 hab
    filter_upwards [hh,hs] with i hi hsi
    simpa only [dite_eq_left hsi] using hi hsi
  · apply Quotient.sound
    exact Filter.Eventually.of_forall fun i => by dsimp only; split_ifs <;> rfl
  · intro x
    induction x using Quotient.inductionOn with
    | h a =>
      apply Quotient.sound
      filter_upwards [hs] with i hi
      simp only [dite_eq_left hi]
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c hm
    apply (localUltraMulRel_mk_iff _ _ _ _ _ _).2
    have hh := (localLargeIndex_eventually_iff U s hs _).1
      ((localUltraMulRel_mk_iff _ _ _ a b c).1 hm)
    filter_upwards [hh,hs] with i hi hsi
    simpa only [dite_eq_left hsi] using hi hsi

theorem localLargeIndex_extend_restrict (x : LocalUltraproduct (U : Filter ι) G) :
    (localLargeIndexExtend U s hs G L).toFun ((localLargeIndexRestrict U s hs G L).toFun x) = x := by
  classical
  induction x using Quotient.inductionOn with
  | h a =>
    apply Quotient.sound
    filter_upwards [hs] with i hi
    simp only [dite_eq_left hi]

theorem localLargeIndex_restrict_extend
    (x : LocalUltraproduct (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val)) :
    (localLargeIndexRestrict U s hs G L).toFun ((localLargeIndexExtend U s hs G L).toFun x) = x := by
  classical
  induction x using Quotient.inductionOn with
  | h a =>
    apply Quotient.sound
    exact Filter.Eventually.of_forall fun j => by
      simp only [dite_eq_left j.property]

theorem localLargeIndex_restrict_mem (A : ∀ i, Set (G i))
    (x : LocalUltraproduct (U : Filter ι) G) :
    (localLargeIndexRestrict U s hs G L).toFun x ∈
      localUltraSet (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val) (fun j => A j.val) ↔
    x ∈ localUltraSet (U : Filter ι) G A := by
  induction x using Quotient.inductionOn with
  | h a =>
    change localUltraMk (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val) (fun j => a j.val) ∈ _ ↔ _
    rw [localUltraMk_mem_iff,localUltraMk_mem_iff]
    exact localLargeIndex_eventually U s hs (fun i => a i ∈ A i)

theorem localLargeIndex_extend_mem (A : ∀ i, Set (G i))
    (x : LocalUltraproduct (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val)) :
    (localLargeIndexExtend U s hs G L).toFun x ∈ localUltraSet (U : Filter ι) G A ↔
    x ∈ localUltraSet (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val) (fun j => A j.val) := by
  rw [← localLargeIndex_restrict_mem U s hs G L A,localLargeIndex_restrict_extend]

/-- The restriction is an actual equivalence of local groups: its inverse
is also a partial homomorphism, and it preserves every internal source set. -/
noncomputable def localLargeIndexEquiv : LocalUltraproduct (U : Filter ι) G ≃
    LocalUltraproduct (localLargeIndexUltrafilter U s hs : Filter s) (fun j => G j.val) where
  toFun := (localLargeIndexRestrict U s hs G L).toFun
  invFun := (localLargeIndexExtend U s hs G L).toFun
  left_inv := localLargeIndex_extend_restrict U s hs G L
  right_inv := localLargeIndex_restrict_extend U s hs G L
end DirectedCycles
