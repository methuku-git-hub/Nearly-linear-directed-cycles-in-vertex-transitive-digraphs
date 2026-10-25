module

public import DirectedCycles.ApproximateIntersectionDensity
public import DirectedCycles.NormalNeighbourhoodAlgebra

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G] [DecidableEq G]

def conjugateSet (S : Finset G) (x : G) : Finset G := S.image (fun g => x*g*x⁻¹)

@[simp] theorem mem_conjugateSet (S : Finset G) (x g : G) :
    g ∈ conjugateSet S x ↔ x⁻¹*g*x ∈ S := by
  simp only [conjugateSet,Finset.mem_image]
  constructor
  · rintro ⟨s,hs,rfl⟩
    convert hs using 1
    group
  · intro h
    exact ⟨x⁻¹*g*x,h,by group⟩

@[simp] theorem card_conjugateSet (S : Finset G) (x : G) :
    (conjugateSet S x).card = S.card :=
  Finset.card_image_of_injective _ (by
    intro a b he
    exact mul_left_cancel (mul_right_cancel he))

theorem conjugate_difference_mem (S : Finset G) (x g : G)
    (hg : g ∈ (conjugateSet S x : Set G)/(conjugateSet S x : Set G)) :
    x⁻¹*g*x ∈ (S : Set G)/(S : Set G) := by
  obtain ⟨a,ha,b,hb,rfl⟩ := hg
  refine ⟨x⁻¹*a*x,(mem_conjugateSet S x a).mp ha,
    x⁻¹*b*x,(mem_conjugateSet S x b).mp hb,?_⟩
  simp only [div_eq_mul_inv]
  group

theorem difference_subset_normalCoreSet (S X D : Finset G) (hX : 1 ∈ X) (hi : S⁻¹ = S)
    (hD : ∀ x ∈ X, (D : Set G)/(D : Set G) ⊆
      (conjugateSet S x : Set G)/(conjugateSet S x : Set G)) :
    (D : Set G)/(D : Set G) ⊆ (normalCoreSet S X : Set G) := by
  have hS : (S : Set G)/(S : Set G) = (S : Set G)^2 := by
    rw [div_eq_mul_inv,← Finset.coe_inv,hi,pow_two]
  have h : ∀ g ∈ (D : Set G)/(D : Set G), ∀ x ∈ X, x⁻¹*g*x ∈ S^2 := by
    intro g hg x hx
    have hh := conjugate_difference_mem S x g (hD x hx hg)
    rw [hS] at hh
    exact_mod_cast hh
  intro g hg
  apply Finset.mem_filter.mpr
  exact ⟨by simpa using h g hg 1 hX,h g hg⟩

theorem card_le_of_difference_subset {D T : Finset G} (hD : D.Nonempty)
    (h : (D : Set G)/(D : Set G) ⊆ (T : Set G)) : D.card ≤ T.card := by
  obtain ⟨d,hd⟩ := hD
  have hs : D.image (fun a => a/d) ⊆ T := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact h ⟨a,ha,d,hd,rfl⟩
  have he : (D.image (fun a => a/d)).card = D.card :=
    Finset.card_image_of_injective D (by intro a b hab; exact div_left_injective hab)
  rw [← he]
  exact Finset.card_le_card hs

/-- Quantitative density of the actual finite normal-core set. -/
theorem normalCoreSet_card_lower_bound (U S X : Finset G) (K δ : ℝ)
    (hU : IsApproximateSubgroup K (U : Set G)) (hδ : 0 < δ)
    (hX : 1 ∈ X) (hi : S⁻¹ = S)
    (hsub : ∀ x ∈ X, conjugateSet S x ⊆ U)
    (hcard : δ*U.card ≤ S.card) :
    (δ/K)^X.card*U.card ≤ (normalCoreSet S X).card := by
  classical
  let l := X.toList.map (conjugateSet S)
  have hlsub : ∀ C ∈ l, C ⊆ U := by
    intro C hC
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hC
    exact hsub x (Finset.mem_toList.mp hx)
  have hlcard : ∀ C ∈ l, δ*U.card ≤ C.card := by
    intro C hC
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hC
    simpa only [card_conjugateSet] using hcard
  obtain ⟨D,hDU,hDcard,hD⟩ := approximate_finite_intersection_density U K δ hU hδ.le l hlsub hlcard
  have hlen : l.length = X.card := by simp [l]
  rw [hlen] at hDcard
  have hDnon : D.Nonempty := Finset.card_pos.mp (by
    have hK : 0 < K := lt_of_lt_of_le zero_lt_one hU.one_le
    have hUc : (0 : ℝ) < U.card := by exact_mod_cast (show U.Nonempty from ⟨1,hU.one_mem⟩).card_pos
    have hl : (0 : ℝ) < (δ/K)^X.card*U.card := by positivity
    have := hl.trans_le hDcard
    exact_mod_cast this)
  have hcore := difference_subset_normalCoreSet S X D hX hi (by
    intro x hx
    exact hD (conjugateSet S x) (List.mem_map.mpr ⟨x,Finset.mem_toList.mpr hx,rfl⟩))
  exact hDcard.trans (by exact_mod_cast card_le_of_difference_subset hDnon hcore)

end FiniteAlmostPeriods
end DirectedCycles
