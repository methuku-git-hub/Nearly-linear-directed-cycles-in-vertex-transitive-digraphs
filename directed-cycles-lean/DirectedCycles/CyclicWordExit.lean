import DirectedCycles.CompactWordLimits
import DirectedCycles.SubgroupNSSBasics

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Elements whose entire nonnegative cyclic orbit lies in the specified set. -/
def cyclicWindowCore (V : Set G) : Set G := {x | ∀ n : ℕ, x^n ∈ V}

theorem cyclicWindowCore_one {V : Set G} (hV : (1 : G) ∈ V) :
    (1 : G) ∈ cyclicWindowCore V := by simpa [cyclicWindowCore]

theorem cyclicWindowCore_subset (V : Set G) : cyclicWindowCore V ⊆ V := by
  intro x hx
  simpa using hx 1

theorem cyclicWindowCore_mono {V W : Set G} (hVW : V ⊆ W) :
    cyclicWindowCore V ⊆ cyclicWindowCore W := fun _ hx n => hVW (hx n)

theorem cyclicWindowCore_symmetric {V : Set G} (hVi : V⁻¹ = V) :
    (cyclicWindowCore V)⁻¹ = cyclicWindowCore V := by
  ext x
  change (∀ n : ℕ, (x⁻¹)^n ∈ V) ↔ (∀ n : ℕ, x^n ∈ V)
  constructor <;> intro hx n
  · have h := Set.inv_mem_inv.mpr (hx n)
    simpa only [hVi,← inv_pow,inv_inv] using h
  · have h := Set.inv_mem_inv.mpr (hx n)
    simpa only [hVi,inv_pow] using h

theorem subgroup_subset_cyclicWindowCore {V : Set G} (S : Subgroup G)
    (hS : (S : Set G) ⊆ V) : (S : Set G) ⊆ cyclicWindowCore V :=
  fun _ hx n => hS (S.pow_mem hx n)

/-- The last fully contained word radius, with the next word power exiting. -/
structure WordExitRadius (Q U : Set G) where
  radius : ℕ
  positive : 0 < radius
  inside : Q^radius ⊆ U
  exits : ¬ Q^(radius+1) ⊆ U
  maximal : ∀ k : ℕ, Q^k ⊆ U → k ≤ radius

/-- Failure of subgroup containment gives an actual first exit, once the
single generator set and the identity lie in the target window. -/
theorem word_exit_radius_exists {Q U : Set G} (hQ1 : (1 : G) ∈ Q)
    (hQi : Q⁻¹ = Q) (hQU : Q ⊆ U)
    (hfail : ¬ (Subgroup.closure Q : Set G) ⊆ U) : Nonempty (WordExitRadius Q U) := by
  classical
  have hex : ∃ k : ℕ, ¬ Q^k ⊆ U := by
    by_contra hn
    push Not at hn
    apply hfail
    intro x hx
    obtain ⟨k,hk⟩ := subgroup_closure_mem_word_power hQi hx
    exact hn k hk
  let r := Nat.find hex
  have hr : ¬ Q^r ⊆ U := Nat.find_spec hex
  have hbefore : ∀ k < r, Q^k ⊆ U := by
    intro k hk
    exact not_not.mp (Nat.find_min hex hk)
  have hr2 : 2 ≤ r := by
    by_contra h
    have hle : r ≤ 1 := by omega
    apply hr
    exact (Set.pow_subset_pow_right hQ1 hle).trans (by simpa using hQU)
  refine ⟨⟨r-1,by omega,hbefore (r-1) (by omega),?_,?_⟩⟩
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hr
  · intro k hk
    by_contra h
    have hrk : r ≤ k := by omega
    exact hr ((Set.pow_subset_pow_right hQ1 hrk).trans hk)

/-- A containing generated subgroup supplies all the subgroup trapping
required at the same ambient window. -/
theorem cyclic_core_subgroup_traps {U V : Set G}
    (h : (Subgroup.closure (cyclicWindowCore V) : Set G) ⊆ U) :
    ∃ H : Subgroup G, (H : Set G) ⊆ U ∧
      ∀ S : Subgroup G, (S : Set G) ⊆ V → S ≤ H := by
  refine ⟨Subgroup.closure (cyclicWindowCore V),h,?_⟩
  intro S hS x hx
  exact Subgroup.subset_closure (subgroup_subset_cyclicWindowCore S hS hx)
end DirectedCycles
