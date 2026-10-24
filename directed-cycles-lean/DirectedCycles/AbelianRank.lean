import DirectedCycles.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.GroupTheory.Rank

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

theorem rank_eq_additive_rank (G : Type*) [Group G] [Group.FG G] :
    Group.rank G = AddGroup.rank (Additive G) := by
  apply le_antisymm
  · obtain ⟨S, hs, hS⟩ := AddGroup.rank_spec (Additive G)
    let T : Finset G := S.image Additive.toMul
    have hT : Subgroup.closure (T : Set G) = ⊤ := by
      apply Subgroup.toAddSubgroup.injective
      rw [Subgroup.toAddSubgroup_closure]
      have he : Additive.toMul ⁻¹' (T : Set G) = (S : Set (Additive G)) := by ext x; simp [T]
      rw [he, hS]
      rfl
    exact (Group.rank_le hT).trans ((Finset.card_image_le).trans_eq hs)
  · obtain ⟨S, hs, hS⟩ := Group.rank_spec G
    let T : Finset (Additive G) := S.image Additive.ofMul
    have hT : AddSubgroup.closure (T : Set (Additive G)) = ⊤ := by
      have he : (T : Set (Additive G)) = Additive.toMul ⁻¹' (S : Set G) := by ext x; simp [T]
      rw [he, ← Subgroup.toAddSubgroup_closure, hS]
      rfl
    exact (AddGroup.rank_le hT).trans ((Finset.card_image_le).trans_eq hs)


/-- A submodule of an r-generated module over a principal ideal domain has at most r generators.
The proof pulls it back to a finite free module and uses Smith normal form. -/
theorem pid_submodule_generators {R M ι : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) (H : Submodule R M) :
    ∃ k : ℕ, k ≤ Fintype.card ι ∧ ∃ w : Fin k → H, Submodule.span R (Set.range w) = ⊤ := by
  let b := Pi.basisFun R ι
  let f : (ι → R) →ₗ[R] M := b.constr R v
  have hf : Function.Surjective f := LinearMap.range_eq_top.mp (by
    change (b.constr R v).range = ⊤
    rw [Module.Basis.constr_range]; exact hv)
  let K := H.comap f
  obtain ⟨k, snf⟩ := K.smithNormalForm b
  let g : K →ₗ[R] H := f.restrict (fun _ h => h)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y.val
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x ∈ H
    rw [hx]
    exact y.property
  refine ⟨k, ?_, fun i => g (snf.bN i), ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective snf.f snf.f.injective
  · have he : Set.range (fun i => g (snf.bN i)) = g '' Set.range snf.bN := Set.range_comp g snf.bN
    rw [he, ← Submodule.map_span, snf.bN.span_eq, Submodule.map_top, LinearMap.range_eq_top.mpr hg]

/-- The additive form of the subgroup generator bound used for central factors. -/
theorem abelian_subgroup_rank_le {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    (H : AddSubgroup A) [AddGroup.FG H] : AddGroup.rank H ≤ AddGroup.rank A := by
  obtain ⟨S, hScard, hS⟩ := AddGroup.rank_spec A
  let v : S → A := Subtype.val
  have hv : Submodule.span ℤ (Set.range v) = ⊤ := by
    have he : Set.range v = (S : Set A) := by ext x; simp [v]
    rw [he, ← AddSubgroup.toIntSubmodule_closure, hS]
    exact AddSubgroup.toIntSubmodule.map_top
  obtain ⟨k, hk, w, hw⟩ := pid_submodule_generators v hv H.toIntSubmodule
  let K := H.toIntSubmodule
  let T : Finset K := Finset.univ.image w
  have hT : AddSubgroup.closure (T : Set K) = ⊤ := by
    have he : (T : Set K) = Set.range w := by simp only [T, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure, he, hw, AddSubgroup.toIntSubmodule.map_top]
  have hcard : T.card ≤ k := (Finset.card_image_le).trans_eq (Fintype.card_fin k)
  have : AddGroup.FG K := AddGroup.fg_iff.mpr ⟨(T : Set K), hT, T.finite_toSet⟩
  have hr := (AddGroup.rank_le hT).trans (hcard.trans (hk.trans_eq (by simpa using hScard)))
  let e : K ≃+ H := {
    toFun := fun x => ⟨x.val, x.property⟩
    invFun := fun x => ⟨x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  rw [← AddGroup.rank_congr e]
  exact hr

/-- The multiplicative finite-abelian subgroup rank bound. -/
theorem finite_abelian_subgroup_rank_le {G : Type*} [CommGroup G] [Finite G]
    (H : Subgroup G) : Group.rank H ≤ Group.rank G := by
  let e : Additive H ≃+ H.toAddSubgroup := {
    toFun := fun x => ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
    invFun := fun x => Additive.ofMul ⟨x.val.toMul, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  rw [rank_eq_additive_rank H, rank_eq_additive_rank G, AddGroup.rank_congr e]
  exact abelian_subgroup_rank_le H.toAddSubgroup

end DirectedCycles
