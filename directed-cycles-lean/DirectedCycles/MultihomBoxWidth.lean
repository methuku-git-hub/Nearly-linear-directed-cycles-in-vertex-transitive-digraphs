module

public import DirectedCycles.MultihomPartialEvaluation
public import DirectedCycles.MultihomGeneration
public import DirectedCycles.FiniteNormalProducts

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles.GroupMultihom

/-- A finite family of genuine separately homomorphic images covers all
values on generating inputs. A common rank bound gives a uniform word
bound for the entire generated image. -/
theorem range_width_of_finite_family {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [CommGroup G] [Finite G]
    (φ : GroupMultihom B G) (S : ∀ i, Set (B i))
    (hS : ∀ i, Subgroup.closure (S i) = ⊤)
    (τ : J → Type*) [∀ j, Fintype (τ j)] [∀ j, DecidableEq (τ j)] [∀ j, Nonempty (τ j)]
    (C : ∀ j, τ j → Type*) [∀ j i, Group (C j i)] [∀ j i, Finite (C j i)]
    (ψ : ∀ j, GroupMultihom (C j) G)
    (hcover : ∀ x, (∀ i, x i ∈ S i) → ∃ j, φ x ∈ Set.range (ψ j))
    (H : Subgroup G) (hH : ∀ j, Set.range (ψ j) ⊆ H)
    (r M : ℕ) (hr : Group.rank H ≤ r) (A : Set G)
    (hA : ∀ j, Set.range (ψ j) ⊆ A^M) :
    (Subgroup.closure (Set.range φ) : Set G) ⊆ A^(Fintype.card J*(M*r)) := by
  let N : J → Subgroup G := fun j => Subgroup.closure (Set.range (ψ j))
  have hn : ∀ j, (N j : Set G) ⊆ A^(M*r) := by
    intro j g hg
    have hw := (ψ j).finite_range_width_in_subgroup H (hH j) r hr hg
    have h := Set.pow_subset_pow_left (n := r) (hA j) hw
    simpa only [← pow_mul] using h
  have hgen : Subgroup.closure (Set.range φ) ≤ ⨆ j, N j := by
    apply (⨆ j, N j).closure_le.mpr
    apply φ.range_le_of_generating_sets S hS
    intro x hx
    obtain ⟨j,hj⟩ := hcover x hx
    exact Subgroup.mem_iSup_of_mem j (Subgroup.subset_closure hj)
  have hbound := finite_normal_sup_power_bound A (⊤ : Subgroup G) N (M*r)
    (fun _ => le_top) (fun j => by rw [Subgroup.normalizer_eq_top]) hn
  exact fun _ hg => hbound (hgen hg)

/-- The restricted map has exactly the prescribed subgroup inputs and
fixed values in the other coordinates. -/
theorem partialEvaluation_subgroup_range {ι : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (s : Set ι) [DecidablePred (· ∈ s)] (x : ∀ i, B i)
    (H : ∀ i, Subgroup (B i)) :
    Set.range ((φ.partialEvaluation s x).subgroupDom (fun i : s => H i.val)) =
      φ '' {z | (∀ i ∈ s, z i ∈ H i) ∧ (∀ i ∉ s, z i = x i)} := by
  ext g
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨fillInputs s x (fun i => (z i).val),⟨?_,?_⟩,rfl⟩
    · intro i hi
      simp [fillInputs,hi]
    · intro i hi
      simp [fillInputs,hi]
  · rintro ⟨z,⟨hz,hfix⟩,rfl⟩
    refine ⟨fun i => ⟨z i.val,hz i.val i.property⟩,?_⟩
    change φ (fillInputs s x (fun i => z i.val)) = φ z
    congr 1
    funext i
    by_cases hi : i ∈ s
    · simp [fillInputs,hi]
    · simp [fillInputs,hi,hfix i hi]

end DirectedCycles.GroupMultihom
