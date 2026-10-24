import DirectedCycles.LocalEscapePowerCutoff
import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalUltraproductEscape
import DirectedCycles.LocalInternalSetLogic
import DirectedCycles.CompactPowerTrapping

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- Every defined source power maps to the corresponding target power. -/
theorem local_model_power_image {G H : Type*} {L : LocalGroupAlgebra G} [Group H]
    (π : LocalGroupHom L (LocalGroupAlgebra.ofGroup H)) {A : Set G} {V : Set H}
    (himage : ∀ z ∈ A, π.toFun z ∈ V) {x : G} {n : ℕ} (hp : L.PowerIn A x n) :
    (π.toFun x)^n ∈ V := by
  obtain ⟨z,hz,hp⟩ := hp
  have he := (LocalGroupAlgebra.ofGroup_product_iff H _ _).1 (hp.map π)
  simp only [List.map_replicate,List.prod_replicate] at he
  exact he ▸ himage z hz

/-- A sufficiently small component escape sublevel maps into any prescribed
open model neighbourhood. Compact NSS trapping supplies a finite cutoff,
and actual power transfer supplies every target power required by it. -/
theorem local_model_escape_sublevel_small {ι : Type*} (U : Ultrafilter ι)
    (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (A : ∀ i, Set (G i)) (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hV : IsCompact V)
    (hNSS : ∀ y : H, (∀ n : ℕ, y^n ∈ V) → y = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (W : Set H) (hWo : IsOpen W) (hW1 : (1 : H) ∈ W) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ localUltraSet (U : Filter ι) G
      (fun i => {x | (L i).escapeNorm (A i) x < r}), π.toFun z ∈ W := by
  obtain ⟨M,_,htrap⟩ := compact_power_trapping hV hNSS hWo hW1
  refine ⟨1/((M : ℝ)+1),by positivity,?_⟩
  intro z hz
  obtain ⟨v,rfl⟩ := Quotient.exists_rep z
  have hv := (localUltraMk_mem_iff (U : Filter ι) G _ v).1 hz
  apply htrap
  intro n hn
  apply local_model_power_image π himage
  apply (localUltraPowerIn_mk_iff (U : Filter ι) G L A v n).2
  filter_upwards [hA,hv] with i hAi hvi
  exact (L i).powerIn_of_escapeNorm_lt hAi hvi n hn
end DirectedCycles
