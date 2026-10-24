import DirectedCycles.LocalPowerSegmentMaps
import DirectedCycles.LocalPowerSequence
import DirectedCycles.LocalInternalSetLogic

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i))

/-- A local target with no nontrivial complete power sequence in the model
window kills the actual infinitesimal generator. All standard powers are
transported as certified products, without evaluating global target powers. -/
theorem local_to_local_model_kills_generator {H : Type*} (Q : LocalGroupAlgebra H)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), N i ≤ M i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H) (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ x ∈ localUltraSet (U : Filter ι) G A, π.toFun x ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G u) = Q.one := by
  let q : Q.PowerSequence (π.toFun (localUltraMk (U : Filter ι) G u)) := {
    power := fun n => π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).power n))
    product := fun n => by
      have hn : ∀ᶠ i in (U : Filter ι), n ≤ M i := by
        filter_upwards [hN n,hM] with i hni hmi
        omega
      simpa only [List.map_replicate] using
        (localUltraSegment_product (U : Filter ι) G L u M p n hn).map π }
  apply hNSS _ q
  intro n
  apply himage
  apply (localUltraMk_mem_iff (U : Filter ι) G A _).2
  filter_upwards [hN n,hprev] with i hni hpi
  exact hpi n hni
end DirectedCycles
