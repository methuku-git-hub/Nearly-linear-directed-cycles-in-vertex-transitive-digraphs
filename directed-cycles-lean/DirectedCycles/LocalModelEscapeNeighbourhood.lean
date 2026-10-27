module

public import DirectedCycles.LocalModelPowerLifting
public import DirectedCycles.LocalUltraproductEscape
public import DirectedCycles.LocalInternalSetLogic
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- A positive component escape sublevel contains the full inverse image of
an open model neighbourhood. Source powers and their domains are lifted from
finitely many target power conditions. -/
theorem local_model_internal_escape_neighbourhood {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H]
    (A : ∀ i, Set (G i))
    (hA : (localUltraAlgebra (U : Filter ι) G L).one ∈ localUltraSet (U : Filter ι) G A)
    (hdom : ∀ x ∈ localUltraSet (U : Filter ι) G A, ∀ y ∈ localUltraSet (U : Filter ι) G A,
      (localUltraAlgebra (U : Filter ι) G L).Defined x y)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (W : Set H) (hWo : IsOpen W) (hW1 : (1 : H) ∈ W)
    (hsmall : ∀ z, π.toFun z ∈ W → z ∈ localUltraSet (U : Filter ι) G A)
    {r : ℝ} (hr : 0 < r) :
    ∃ V : Set H, IsOpen V ∧ (1 : H) ∈ V ∧ V ⊆ W ∧
      ∀ z, π.toFun z ∈ V → z ∈ localUltraSet (U : Filter ι) G (fun i => {x | (L i).escapeNorm (A i) x < r}) := by
  obtain ⟨M,hM⟩ := exists_nat_one_div_lt hr
  let V : Set H := ⋂ j : Fin (M+2), {x | x^j.val ∈ W}
  have hVo : IsOpen V := isOpen_iInter_of_finite (fun j => hWo.preimage (continuous_pow j.val))
  have hV1 : (1 : H) ∈ V := by
    apply Set.mem_iInter.mpr
    intro j
    simpa using hW1
  have hVW : V ⊆ W := by
    intro y hy
    simpa using Set.mem_iInter.mp hy ⟨1,by omega⟩
  refine ⟨V,hVo,hV1,hVW,?_⟩
  intro z hz
  have hzA := hsmall z (hVW hz)
  have hp := (localUltraAlgebra (U : Filter ι) G L).powerIn_of_model_powers
    (localUltraSet (U : Filter ι) G A) hA hdom π W hsmall hzA M
    (fun n hn => Set.mem_iInter.mp hz ⟨n,by omega⟩)
  obtain ⟨v,rfl⟩ := Quotient.exists_rep z
  have each : ∀ j : Fin (M+1), ∀ᶠ i in (U : Filter ι), (L i).PowerIn (A i) (v i) j.val :=
    fun j => (localUltraPowerIn_mk_iff _ G L A v j.val).1 (hp j.val (by omega))
  have hall := Filter.eventually_all.mpr each
  apply (localUltraMk_mem_iff (U : Filter ι) G _ v).2
  filter_upwards [hall] with i hi
  exact lt_of_le_of_lt ((L i).escapeNorm_le_of_powers (n := M) (fun n hn => hi ⟨n,by omega⟩)) hM
end DirectedCycles
