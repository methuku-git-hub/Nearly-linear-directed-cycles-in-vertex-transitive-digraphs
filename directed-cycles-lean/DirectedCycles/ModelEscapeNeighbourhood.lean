module

public import DirectedCycles.GroupUltraproduct
public import DirectedCycles.UltraproductInternalSets
public import DirectedCycles.EscapeSublevelPowers
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- Every fixed positive escape sublevel contains the inverse image of an open
model neighbourhood. Only finitely many powers need to be tested. -/
theorem model_escapeSublevel_neighbourhood {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (A : ∀ i, Set (G i))
    (S : Subgroup (GroupUltraproduct (U : Filter ι) G)) (π : S →* H)
    (W : Set H) (hWo : IsOpen W) (hW1 : (1 : H) ∈ W)
    (hsmall : ∀ z : S, π z ∈ W → z.val ∈ ultraSet (U : Filter ι) G A)
    {r : ℝ} (hr : 0 < r) :
    ∃ V : Set H, IsOpen V ∧ (1 : H) ∈ V ∧
      ∀ z : S, π z ∈ V → z.val ∈ ultraSet (U : Filter ι) G (fun i => escapeSublevel (A i) r) := by
  obtain ⟨M,hM⟩ := exists_nat_one_div_lt hr
  let V : Set H := ⋂ j : Fin (M+1), {x | x^(j.val) ∈ W}
  have hVo : IsOpen V := isOpen_iInter_of_finite (fun j => hWo.preimage (continuous_pow j.val))
  have hV1 : (1 : H) ∈ V := by
    apply Set.mem_iInter.mpr
    intro j
    simpa using hW1
  refine ⟨V,hVo,hV1,?_⟩
  intro z hz
  obtain ⟨v,hv⟩ := ultraMk_surjective (U : Filter ι) G z.val
  have hp : ∀ j : Fin (M+1), ∀ᶠ i in (U : Filter ι), (v i)^j.val ∈ A i := by
    intro j
    apply (ultraMk_mem_ultraSet_iff _ G A _).1
    change ultraMk (U : Filter ι) G (v^j.val) ∈ ultraSet (U : Filter ι) G A
    rw [map_pow,hv]
    exact hsmall (z^j.val) (by
      rw [map_pow]
      exact Set.mem_iInter.mp hz j)
  have hall := (Filter.eventually_all).2 hp
  rw [← hv]
  apply (ultraMk_mem_ultraSet_iff _ G _ _).2
  filter_upwards [hall] with i hi
  apply le_trans (escapeNorm_le_of_powers (n := M) _) hM.le
  intro n hn
  exact hi ⟨n,by omega⟩
end DirectedCycles
