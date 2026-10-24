import DirectedCycles.LocalCentralProgressionFamily
import DirectedCycles.LocalShortProgressionModel

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace DirectedCycles

/-- The finite data supplied by the actual central Lie reduction discharge
every window, kernel, centrality and density premise of progression lifting.
The source central generator is retained, and its inner membership is
proved from the escape bound on the relevant large set of components. -/
theorem local_central_progression_family_from_windows {ι : Type*} (F : Filter ι)
    (G : ι → Type*) [∀ i, Fintype (G i)] (L : ∀ i, LocalGroupAlgebra (G i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A B P : ∀ i, Finset (G i))
    (D : ∀ i, (L i).CentralQuotientData (P i : Set (G i))) {Ka K J Jq r c : ℕ}
    (hA : ∀ i, IsLocalFiniteApproximateGroup (L i) Ka (A i))
    (hJ : 1 ≤ J) (hJq : 1 ≤ Jq) {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hB : ∀ᶠ i in F, IsStrongLocalFiniteApproximateGroup (L i) K (B i))
    (hBA : ∀ i, (B i : Set (G i)) ⊆ A i)
    (hBpower : ∀ i, ∀ m ≤ 200, (L i).wordPower (B i : Set (G i)) m ⊆ (D i).small)
    (τ : ℝ) (hDescape : ∀ i, (D i).small ⊆ {x | (L i).escapeNorm (A i) x < τ})
    (hPlocal : ∀ i, (L i).CentralLocalSet (P i : Set (G i))
      {x | (L i).escapeNorm (A i) x < 1/1001} {x | (L i).escapeNorm (A i) x < τ})
    (hcontrol : ∀ᶠ i in F, ∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small,
      x.val ∈ B i ∧ (D i).project x = y ∧ (L i).escapeNorm (B i) x.val ≤
        C*(D i).algebra.escapeNorm ((D i).finiteImage (B i)) y)
    (u : ∀ i, G i) (n : ι → ℕ) (p : ∀ i, (L i).PowerSegment (u i) (2*n i))
    (hn2 : ∀ i, 2 ≤ n i) (hu : ∀ i, u i ≠ (L i).one)
    (hescape : ∀ᶠ i in F, (L i).escapeNorm (B i) (u i) ≤ C₀/((n i : ℝ)+1))
    (hNSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (hprev : ∀ i, ∀ m < n i, (p i).power m ∈ A i)
    (hPexact : ∀ i, (P i : Set (G i)) = (p i).shortSignedSet (n i))
    (hPcard : ∀ i, (P i).card = 2*n i-1)
    (hcard : ∀ᶠ i in F, (A i).card ≤ J*((D i).finiteImage (B i)).card*(P i).card)
    (g : ∀ i, Fin r → (D i).Carrier) (N : ι → Fin r → ℕ)
    (hN : ∀ j, Filter.Tendsto (fun i => N i j) F Filter.atTop)
    (hn : ∀ m : ℕ, ∀ᶠ i in F, m < n i)
    (hquot : ∀ᶠ i in F, ∃ hq : (D i).algebra.SignedWordsIn (g i) (N i) ((D i).finiteImage (B i)),
      Function.Injective ((D i).algebra.orderedGrid hq) ∧
      (∀ x, (D i).algebra.GeneratorCommutators (Set.range (g i)) c x → x = (D i).algebra.one) ∧
      ((D i).finiteImage (B i)).card ≤ Jq * ∏ j, (2*N i j+1)) :
    ∃ T M : ℕ, 3 ≤ T ∧ 1 ≤ M ∧
      (∀ j : Fin (r+1), Filter.Tendsto (fun i => (Fin.lastCases (n i) (N i) j)/T) F Filter.atTop) ∧
      ∀ᶠ i in F, ∃ W : (L i).ProgressionWitness (A i : Set (G i)) (r+1) (c+1),
        W.lengths = (fun j => (Fin.lastCases (n i) (N i) j)/T) ∧
        (A i).card ≤ M * ∏ j, (2*W.lengths j+1) := by
  have hBD : ∀ i, (B i : Set (G i)) ⊆ (D i).small := by
    intro i
    simpa only [LocalGroupAlgebra.wordPower_one] using hBpower i 1 (by omega)
  have hcentral : ∀ i, ∀ x ∈ (P i : Set (G i)), ∀ b ∈ B i, (L i).Commute x b := by
    intro i x hx b hb
    exact (hPlocal i).central x hx b (hDescape i (hBD i hb))
  have hkernel : ∀ i, ∀ k : ℤ, k.natAbs < n i → (p i).signedPower k ∈ (P i : Set (G i)) := by
    intro i k hk
    rw [hPexact i]
    exact ⟨k,hk,rfl⟩
  have hdom : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, (L i).Defined x y := by
    intro i x hx y hy
    obtain ⟨z,hz⟩ := (hA i).allProducts [x,y] (by simp) (by aesop)
    exact ⟨z,(LocalGroupAlgebra.Product.pair_iff (L i) x y z).1 hz⟩
  have hcard' : ∀ᶠ i in F, (A i).card ≤ J*((D i).finiteImage (B i)).card*(2*n i-1) := by
    filter_upwards [hcard] with i hi
    simpa only [hPcard i] using hi
  have hn' : Filter.Tendsto n F Filter.atTop :=
    Filter.tendsto_atTop.2 (fun m => (hn m).mono (fun _ h => h.le))
  exact local_central_progression_family F G L hd hr A B (fun i => (P i : Set (G i))) D
    hJ hJq hC hC₀ hB hBA hBD hcontrol hcentral u n p hn2 hu hescape hNSS hdom hprev hkernel
    hcard' g N hN hn' hquot
end DirectedCycles
