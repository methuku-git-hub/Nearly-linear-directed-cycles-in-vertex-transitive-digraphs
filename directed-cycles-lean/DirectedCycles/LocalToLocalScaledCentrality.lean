import DirectedCycles.LocalScaledModel
import DirectedCycles.LocalSignedPowerCommutation


set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- The local curve from finite segments commutes with an actual target
neighbourhood when the generator centralizes its internal inverse image. -/
theorem local_to_local_scaled_curve_central {H : Type*} (Q : LocalGroupAlgebra H)
    (hd : ∀ i, (L i).DivisionClosed)
    (A C : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ᶠ i in (U : Filter ι), 3 ≤ N i ∧ N i ≤ M i)
    (hu : ∀ᶠ i in (U : Filter ι), u i ∈ A i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hdom : ∀ᶠ i in (U : Filter ι), (L i).AllProductsDefined (A i) 3)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hcomm : ∀ᶠ i in (U : Filter ι), ∀ v ∈ C i, v ∈ A i ∧ (L i).Commute v (u i))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (φ : ℝ → H)
    (hformula : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t))
    (W : Set H)
    (hthick : ∀ y ∈ W, ∃ z, z ∈ localUltraSet (U : Filter ι) G C ∧ π.toFun z = y) :
    ∀ t : ℝ, |t| ≤ 1/2 → ∀ y ∈ W, Q.Commute (φ t) y := by
  intro t ht y hy
  obtain ⟨z,hz,hzy⟩ := hthick y hy
  obtain ⟨v,rfl⟩ := Quotient.exists_rep z
  have hv := (localUltraMk_mem_iff (U : Filter ι) G C v).1 hz
  have hc : ∀ᶠ i in (U : Filter ι), (L i).Commute (v i)
      ((p i).signedPower (Int.floor (t*(N i : ℝ)))) := by
    filter_upwards [hN,hu,hi,hdom,hprev,hcomm,hv] with i hNi hui hii hdi hpi hci hvi
    have hk := scaled_floor_natAbs_lt t (N i) ht hNi.1
    exact (p i).commute_signedPower (L i) (hd i) hii hdi hui (hci _ hvi).1 (hci _ hvi).2
      _ (by omega) (fun n hn => hpi n (by omega))
  have hc' := localUltraCommute_mk U G L v
    (fun i => (p i).signedPower (Int.floor (t*(N i : ℝ)))) hc
  obtain ⟨q,hq,hq'⟩ := hc'
  have hm : Q.Commute (π.toFun (localScaledPower U G L u N M p t)) (π.toFun (localUltraMk (U : Filter ι) G v)) :=
    ⟨π.toFun q,π.map_mul hq',π.map_mul hq⟩
  rw [hformula t (by linarith),← hzy]
  exact hm
end DirectedCycles
