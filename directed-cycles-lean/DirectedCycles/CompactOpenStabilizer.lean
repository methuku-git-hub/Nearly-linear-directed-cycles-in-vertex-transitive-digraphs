import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The actual subgroup preserving membership in a set under left translation. -/
def leftSetStabilizer (S : Set G) : Subgroup G where
  carrier := {g | ∀ x : G, g*x ∈ S ↔ x ∈ S}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x
    rw [mul_assoc,hg (h*x),hh x]
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹*x)
    simpa only [mul_inv_cancel_left] using h.symm

theorem leftSetStabilizer_subset {S : Set G} (h1 : (1 : G) ∈ S) :
    (leftSetStabilizer S : Set G) ⊆ S := by
  intro g hg
  have h := (hg 1).2 h1
  simpa only [mul_one] using h

/-- A compact open set has an open translation stabilizer. Compactness makes
one identity neighbourhood act uniformly on the whole set. -/
theorem leftSetStabilizer_isOpen [TopologicalSpace G] [IsTopologicalGroup G]
    {S : Set G} (hc : IsCompact S) (ho : IsOpen S) :
    IsOpen (leftSetStabilizer S : Set G) := by
  have hprod : ({1} : Set G) ×ˢ S ⊆ (fun p : G × G => p.1*p.2) ⁻¹' S := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have he : x = 1 := hx
    simpa only [Set.mem_preimage,he,one_mul] using hy
  obtain ⟨U,V,hU,hV,h1,hSV,hUV⟩ := generalized_tube_lemma isCompact_singleton hc
    (ho.preimage continuous_mul) hprod
  have hU1 : (1 : G) ∈ U := h1 rfl
  have hW : U ∩ U⁻¹ ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (hU.mem_nhds hU1)
      ((hU.preimage continuous_inv).mem_nhds (by simpa only [Set.mem_preimage,inv_one] using hU1))
  apply (leftSetStabilizer S).isOpen_of_mem_nhds
  apply Filter.mem_of_superset hW
  intro g hg x
  have hleft : ∀ z ∈ S, g*z ∈ S := by
    intro z hz
    exact hUV (show (g,z) ∈ U ×ˢ V from ⟨hg.1,hSV hz⟩)
  have hright : ∀ z ∈ S, g⁻¹*z ∈ S := by
    intro z hz
    exact hUV (show (g⁻¹,z) ∈ U ×ˢ V from ⟨hg.2,hSV hz⟩)
  constructor
  · intro hx
    simpa only [inv_mul_cancel_left] using hright (g*x) hx
  · exact hleft x

/-- Every compact open identity neighbourhood contains an actual compact
open subgroup, its translation stabilizer. -/
theorem compact_open_subgroup_of_compact_open [TopologicalSpace G] [IsTopologicalGroup G]
    {S : Set G} (hc : IsCompact S) (ho : IsOpen S) (h1 : (1 : G) ∈ S) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsCompact (H : Set G) ∧ (H : Set G) ⊆ S := by
  have hHo := leftSetStabilizer_isOpen hc ho
  have hHS := leftSetStabilizer_subset h1
  exact ⟨leftSetStabilizer S,hHo,hc.of_isClosed_subset
    ((leftSetStabilizer S).isClosed_of_isOpen hHo) hHS,hHS⟩
end DirectedCycles
