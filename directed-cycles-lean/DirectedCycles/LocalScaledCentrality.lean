import DirectedCycles.LocalScaledModel
import DirectedCycles.LocalSignedPowerCommutation
import DirectedCycles.ScaledCurveCentrality

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- Centrality on a real interval propagates to every parameter by taking
standard powers; centrality on an identity neighbourhood propagates through
the connected target group. -/
theorem curve_central_of_local_interval {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [PreconnectedSpace H]
    (φ : ℝ → H) (h0 : φ 0 = 1) (hadd : ∀ s t, φ (s+t) = φ s*φ t)
    {W : Set H} (hW : W ∈ 𝓝 (1 : H))
    (hc : ∀ t : ℝ, |t| ≤ 1/2 → ∀ y ∈ W, Commute (φ t) y) :
    ∀ t : ℝ, ∀ y : H, Commute (φ t) y := by
  intro t y
  obtain ⟨n,hn⟩ := exists_nat_gt (2*|t|)
  have hnR : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have ht : |t/(n : ℝ)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos hnR]
    apply (div_le_iff₀ hnR).2
    linarith
  have hcomm : Commute (φ (t/(n : ℝ))) y :=
    commute_of_commutes_neighbourhood _ hW (hc _ ht) y
  have he : (n : ℝ)*(t/(n : ℝ)) = t := by field_simp
  have hp := real_additive_curve_nat_mul φ h0 hadd (t/(n : ℝ)) n
  rw [he] at hp
  rw [hp]
  exact hcomm.pow_left n

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- The curve constructed from actual finite local segments is central when
the generator centralizes an internal source neighbourhood. -/
theorem local_scaled_curve_central {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [PreconnectedSpace H]
    (hd : ∀ i, (L i).DivisionClosed)
    (A C : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ᶠ i in (U : Filter ι), 3 ≤ N i ∧ N i ≤ M i)
    (hu : ∀ᶠ i in (U : Filter ι), u i ∈ A i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hdom : ∀ᶠ i in (U : Filter ι), (L i).AllProductsDefined (A i) 3)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hcomm : ∀ᶠ i in (U : Filter ι), ∀ v ∈ C i, v ∈ A i ∧ (L i).Commute v (u i))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (φ : ℝ → H) (h0 : φ 0 = 1) (hadd : ∀ s t, φ (s+t) = φ s*φ t)
    (hformula : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t))
    (W : Set H) (hW : W ∈ 𝓝 (1 : H))
    (hthick : ∀ y ∈ W, ∃ z, z ∈ localUltraSet (U : Filter ι) G C ∧ π.toFun z = y) :
    ∀ t : ℝ, ∀ y : H, Commute (φ t) y := by
  apply curve_central_of_local_interval φ h0 hadd hW
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
  have hm := hc'.map (localUltraAlgebra (U : Filter ι) G L) π
  rw [hformula t (by linarith),← hzy]
  exact hm.symm
end DirectedCycles
