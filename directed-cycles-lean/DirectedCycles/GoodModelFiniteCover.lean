module

public import DirectedCycles.InternalGoodModel
public import DirectedCycles.OpenSubgroupGoodModel
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
universe u
variable {G : Type u} [Group G] {T : Set G} {Internal : Set G → Prop}

/-- Compact model images and an actual inner preimage give a finite
translate cover in the original source group. -/
theorem good_model_finite_cover
    (M : InternalLocallyCompactGroupModel G T Internal) (B : Set G)
    (V : Set M.carrier) (hV : IsOpen V) (hV1 : (1 : M.carrier) ∈ V)
    (hVB : M.map ⁻¹' V ⊆ B) :
    ∃ F : Finset G, T ⊆ (F : Set G)*B := by
  classical
  let cells : G → Set M.carrier := fun g => (fun y => M.map g*y) '' V
  have hcells : ∀ g, IsOpen (cells g) := fun g => isOpenMap_mul_left (M.map g) V hV
  have hcover : M.map '' T ⊆ ⋃ g : G, cells g := by
    intro y _
    obtain ⟨g,rfl⟩ := M.surjective y
    exact Set.mem_iUnion.mpr ⟨g,1,hV1,mul_one _⟩
  obtain ⟨F,hF⟩ := M.compact_image.elim_finite_subcover cells hcells hcover
  refine ⟨F,?_⟩
  intro x hx
  obtain ⟨g,hg,y,hy,he⟩ := Set.mem_iUnion₂.mp (hF ⟨x,hx,rfl⟩)
  have hm : g⁻¹*x ∈ B := by
    apply hVB
    change M.map (g⁻¹*x) ∈ V
    rw [map_mul,map_inv,← he,inv_mul_cancel_left]
    exact hy
  exact ⟨g,hg,g⁻¹*x,hm,mul_inv_cancel_left g x⟩

/-- Restricting a good model to an open target subgroup retains a finite
translate cover of the original modelled set by the actual restricted set. -/
theorem good_model_open_restriction_cover
    (M : InternalLocallyCompactGroupModel G T Internal)
    (S : Subgroup M.carrier) (hS : IsOpen (S : Set M.carrier)) :
    ∃ F : Finset G, T ⊆ (F : Set G)*(T ∩ (S.comap M.map : Set G)) := by
  apply good_model_finite_cover M _ (M.neighbourhood ∩ (S : Set M.carrier))
    (M.open_neighbourhood.inter hS) ⟨M.one_mem_neighbourhood,S.one_mem⟩
  intro x hx
  exact ⟨M.small_neighbourhood hx.1,hx.2⟩
end DirectedCycles
