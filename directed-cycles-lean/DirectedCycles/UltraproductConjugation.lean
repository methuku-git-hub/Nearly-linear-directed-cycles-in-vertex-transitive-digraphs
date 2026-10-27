module

public import DirectedCycles.UltraproductInternalSets

@[expose] public section

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- Pointwise conjugation inclusions transfer to the actual internal sets. -/
theorem ultraSet_conjugation_subset {ι : Type*} (f : Filter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (A B C : ∀ i, Set (G i))
    (h : ∀ᶠ i in f, ∀ x ∈ A i, ∀ g ∈ B i, x⁻¹*g*x ∈ C i) :
    ∀ x ∈ ultraSet f G A, ∀ g ∈ ultraSet f G B, x⁻¹*g*x ∈ ultraSet f G C := by
  intro x hx g hg
  obtain ⟨a,rfl⟩ := ultraMk_surjective f G x
  obtain ⟨b,rfl⟩ := ultraMk_surjective f G g
  have ha := (ultraMk_mem_ultraSet_iff f G A a).mp hx
  have hb := (ultraMk_mem_ultraSet_iff f G B b).mp hg
  rw [← map_inv,← map_mul,← map_mul]
  apply (ultraMk_mem_ultraSet_iff f G C (a⁻¹*b*a)).mpr
  filter_upwards [ha,hb,h] with i hi hj hk
  exact hk (a i) hi (b i) hj

end DirectedCycles
