import DirectedCycles.AbelianExponent
import Mathlib.GroupTheory.Index

set_option autoImplicit false
open scoped BigOperators Classical
namespace DirectedCycles

/-- A finite generating family killed by a positive integer makes an
abelian group finite. The proof constructs a surjection from a finite power
of ZMod, so finiteness is a conclusion, not an assumption. -/
theorem abelian_finite_of_generators_exponent {A ι : Type*} [AddCommGroup A]
    [Fintype ι] (v : ι → A) (hv : AddSubgroup.closure (Set.range v) = ⊤)
    (e : ℕ) (he : 0 < e) (hexp : ∀ i, e • v i = 0) : Finite A := by
  let : NeZero e := ⟨by omega⟩
  let f : ι → (ZMod e →+ A) := fun i => ZMod.lift e
    ⟨{ toFun := fun z => z • v i
       map_zero' := zero_zsmul _
       map_add' := fun x y => add_zsmul (v i) x y }, by simpa using hexp i⟩
  let F : (ι → ZMod e) →+ A := {
    toFun := fun w => ∑ i, f i (w i)
    map_zero' := by simp
    map_add' := by intro x y; simp only [Pi.add_apply,map_add,Finset.sum_add_distrib] }
  have hgen : ∀ i, v i ∈ F.range := by
    intro i
    refine ⟨Pi.single i 1,?_⟩
    change (∑ j, f j ((Pi.single i 1 : ι → ZMod e) j)) = v i
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same]
      calc f i 1 = f i ((1 : ℤ) : ZMod e) := by norm_num
           _ = (1 : ℤ) • v i := ZMod.lift_coe e _ _
           _ = v i := one_zsmul _
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji,map_zero]
    · simp
  have hs : Function.Surjective F := AddMonoidHom.range_eq_top.mp (by
    apply top_unique
    rw [← hv]
    exact F.range.closure_le.mpr (by rintro _ ⟨i,rfl⟩; exact hgen i))
  exact Finite.of_surjective F hs

/-- A positive multiplier into a subgroup bounds its index by the multiplier
raised to the number of generators of the ambient abelian group. -/
theorem additive_index_le_multiplier {A ι : Type*} [AddCommGroup A]
    [Fintype ι] (v : ι → A) (hv : AddSubgroup.closure (Set.range v) = ⊤)
    (H : AddSubgroup A) (M : ℕ) (hM : 0 < M) (h : ∀ x, M • x ∈ H) :
    H.index ≤ M^Fintype.card ι := by
  let q := QuotientAddGroup.mk' H
  let w := fun i => q (v i)
  have hw : AddSubgroup.closure (Set.range w) = ⊤ := by
    change AddSubgroup.closure (Set.range (q ∘ v)) = ⊤
    rw [Set.range_comp,← AddMonoidHom.map_closure,hv]
    exact AddSubgroup.map_top_of_surjective q (QuotientAddGroup.mk'_surjective H)
  have hexp : ∀ i, M • w i = 0 := by
    intro i
    change M • q (v i) = 0
    rw [← map_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr (h (v i))
  let _ : Finite (A ⧸ H) := abelian_finite_of_generators_exponent w hw M hM hexp
  let _ := Fintype.ofFinite (A ⧸ H)
  have hc := abelian_card_le_exponent_pow_generators w hw M hM hexp
  simpa only [AddSubgroup.index,Nat.card_eq_fintype_card] using hc

end DirectedCycles
