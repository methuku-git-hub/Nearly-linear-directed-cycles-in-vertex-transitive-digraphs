module

public import DirectedCycles.NilpotentCycles
public import DirectedCycles.CayleyStrongConnectivity

@[expose] public section

set_option autoImplicit false
universe u
namespace DirectedCycles

theorem cayley_stronglyConnected_generates {G : Type*} [Group G]
    (S : Set G) (hsc : StronglyConnected (CayleyDigraph S)) : Subgroup.closure S = ⊤ := by
  apply top_le_iff.mp
  intro g hg
  clear hg
  have h := hsc 1 g
  induction h with
  | refl => exact Subgroup.one_mem _
  | tail h hxy ih =>
    obtain ⟨s,hs,he⟩ := hxy
    rw [he]
    exact Subgroup.mul_mem _ ih (Subgroup.subset_closure hs)

/-- The public nilpotent theorem supplies a uniform genuine-cycle bound
on all layer graphs with at least two layers. -/
theorem nilpotent_uniform_layer_bound (r c : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ b : ℝ, 0 < b ∧ ∀ (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G],
      Group.rank G ≤ r → Group.nilpotencyClass G ≤ c → LayerCycleLowerBound G b eta := by
  obtain ⟨b,hb,h⟩ := nilpotent_cycle_theorem.{u} r c eta heta
  refine ⟨b,hb,?_⟩
  intro G _ _ _ hr hc T hT S hS hsc
  rcases (h G hr hc).2 T (by omega) S hS hsc with hC | hloop
  · exact hC
  · exact (by omega : False).elim

end DirectedCycles
