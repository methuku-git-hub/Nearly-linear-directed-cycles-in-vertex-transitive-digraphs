module

public import DirectedCycles.ActionBallCardinality
public import DirectedCycles.ShortSchreierGeneration

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- An injective group map reflects approximate-subgroup structure when
the approximate set is exactly its image. -/
theorem approximate_of_injective_image {G A : Type*} [Group G] [Group A]
    (f : G →* A) (hf : Function.Injective f) (S : Set G) (K : ℝ)
    (h : IsApproximateSubgroup K (f '' S)) : IsApproximateSubgroup K S := by
  classical
  have h1 : (1 : G) ∈ S := by
    obtain ⟨g,hg,he⟩ := h.one_mem
    have he' : g = 1 := hf (he.trans (map_one f).symm)
    exact he' ▸ hg
  have hi : S⁻¹ = S := by
    apply Set.image_injective.mpr hf
    rw [Set.image_inv,h.inv_eq_self]
  refine ⟨h1,hi,?_⟩
  obtain ⟨F,hF,hcov⟩ := h.sq_covBySMul
  let T := F.preimage f hf.injOn
  refine ⟨T,?_,?_⟩
  · have hc : T.card ≤ F.card := by
      dsimp only [T]
      rw [Finset.card_preimage]
      exact Finset.card_filter_le _ _
    exact (by exact_mod_cast hc : (T.card : ℝ) ≤ F.card).trans hF
  · intro x hx
    have him : f x ∈ (f '' S)^2 := by rw [← Set.image_pow]; exact ⟨x,hx,rfl⟩
    obtain ⟨a,ha,b,⟨y,hy,hfy⟩,he⟩ := hcov him
    have hpre : f (x*y⁻¹) = a := by
      rw [map_mul,map_inv,← he,← hfy]
      change a*f y*(f y)⁻¹ = a
      group
    refine ⟨x*y⁻¹,?_,y,hy,?_⟩
    · change x*y⁻¹ ∈ T
      simp only [T,Finset.mem_preimage,hpre]
      exact ha
    · change (x*y⁻¹)*y = x
      group

theorem subtype_image_preimage {G : Type*} [Group G] (N : Subgroup G) (S : Set G) :
    N.subtype '' (N.subtype ⁻¹' S) = S ∩ (N : Set G) := by
  ext g
  constructor
  · rintro ⟨a,ha,rfl⟩; exact ⟨ha,a.property⟩
  · rintro ⟨hg,hN⟩; exact ⟨⟨g,hN⟩,hg,rfl⟩

theorem short_subgroup_preimage_generates {G : Type*} [Group G] [Finite G]
    (S : Set G) (h1 : 1 ∈ S) (hi : S⁻¹ = S) (hgen : Subgroup.closure S = ⊤)
    (N : Subgroup G) [N.Normal] (p : ℕ) (hp : 2*N.index+1 ≤ p) :
    Subgroup.closure (N.subtype ⁻¹' (S^p)) = ⊤ := by
  have hclosure : Subgroup.closure (S^p ∩ (N : Set G)) = N := by
    apply le_antisymm (N.closure_le.mpr Set.inter_subset_right)
    calc
      N = Subgroup.closure (S^(2*N.index+1) ∩ (N : Set G)) :=
        (short_normal_subgroup_generation S h1 hi hgen N).symm
      _ ≤ Subgroup.closure (S^p ∩ (N : Set G)) :=
        Subgroup.closure_mono (Set.inter_subset_inter_left _ (Set.pow_subset_pow_right h1 hp))
  apply Subgroup.map_injective N.subtype_injective
  rw [MonoidHom.map_closure,subtype_image_preimage,hclosure,Subgroup.map_top,N.range_subtype]

/-- Intersecting a sufficiently large approximate power with a subgroup
gives an approximate group in the subgroup's own type. -/
theorem approximate_power_subgroup_preimage {G : Type*} [Group G]
    (A : Set G) (K : ℝ) (hA : IsApproximateSubgroup K A) (N : Subgroup G)
    (p : ℕ) (hp : 2 ≤ p) :
    IsApproximateSubgroup (K^(2*p-1)) (N.subtype ⁻¹' (A^p)) := by
  apply approximate_of_injective_image N.subtype N.subtype_injective
  rw [subtype_image_preimage]
  have hh := hA.pow_inter_pow (IsApproximateSubgroup.subgroup (H := N)) hp (by omega : 2 ≤ 2)
  simpa [sq] using hh

end DirectedCycles
