import DirectedCycles.LocalModelEscapeControl
import DirectedCycles.LocalEscapeMaps

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- Uniform trapping of actual local powers in a local target controls
component escape sublevels. The target need not be a global group. -/
theorem local_to_local_model_escape_sublevel_small {ι : Type*} (U : Ultrafilter ι)
    (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    {H : Type*} [TopologicalSpace H] (M : LocalGroupAlgebra H)
    (A : ∀ i, Set (G i)) (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    (V : Set H)
    (htrap : ∀ W : Set H, W ∈ 𝓝 M.one → ∃ N : ℕ, 1 ≤ N ∧
      ∀ y : H, (∀ n ≤ N, M.PowerIn V y n) → y ∈ W)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (W : Set H) (hW : W ∈ 𝓝 M.one) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ localUltraSet (U : Filter ι) G
      (fun i => {x | (L i).escapeNorm (A i) x < r}), π.toFun z ∈ W := by
  obtain ⟨N,_,hsmall⟩ := htrap W hW
  refine ⟨1/((N : ℝ)+1),by positivity,?_⟩
  intro z hz
  obtain ⟨v,rfl⟩ := Quotient.exists_rep z
  have hv := (localUltraMk_mem_iff (U : Filter ι) G _ v).1 hz
  apply hsmall
  intro n hn
  have hp : (localUltraAlgebra (U : Filter ι) G L).PowerIn
      (localUltraSet (U : Filter ι) G A) (localUltraMk (U : Filter ι) G v) n := by
    apply (localUltraPowerIn_mk_iff (U : Filter ι) G L A v n).2
    filter_upwards [hA,hv] with i hAi hvi
    exact (L i).powerIn_of_escapeNorm_lt hAi hvi n hn
  obtain ⟨y,hy,hprod⟩ := hp
  refine ⟨π.toFun y,himage y hy,?_⟩
  simpa only [List.map_replicate] using hprod.map π
end DirectedCycles
