module

public import DirectedCycles.StrongLocalCentralProgression
public import DirectedCycles.StrongLocalUniformNSSQuotient
public import DirectedCycles.LocalSignedProgressionClosure
public import DirectedCycles.LocalCentralEquivalence
public import DirectedCycles.LocalEscapePowerCutoff

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Uniform central local closure of the actual first-exit progression.
The closure region is a fixed escape cutoff and the centralizing region
has a radius depending only on K. -/
theorem strong_local_central_set (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G) (A : Finset G),
        IsStrongLocalFiniteApproximateGroup L K A → L.DivisionClosed → L.Reversible →
        L.IsNSS (A : Set G) → (∃ g ∈ A, g ≠ L.one) →
        ∃ N : ℕ, 2 ≤ N ∧ ∃ P : Finset G, P.card = 2*N-1 ∧ (P : Set G) ⊆ A ∧
          L.CentralLocalSet (P : Set G) {x | L.escapeNorm A x < 1/1001}
            {x | L.escapeNorm A x < δ} := by
  obtain ⟨δ,hδ,hδhalf,hprog⟩ := strong_local_central_progression K
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro G _ L A hA hd hr hNSS hne
  obtain ⟨u,_,_,N,hN,p,hmem,⟨z,hz,hzout⟩,_,hcard,hsub,h1,hi,hcentral⟩ :=
    hprog G L A hA hd hr hNSS hne
  refine ⟨N,hN,p.signedProgression L,hcard,hsub,?_⟩
  refine ⟨h1,hi,?_,?_⟩
  · intro x hx y hy v hv hmul
    change L.escapeNorm A v < 1/1001 at hv
    have hreturn : ∀ j ≤ 1000, L.PowerIn (A : Set G) v j :=
      L.powerIn_of_escapeNorm_lt hA.approximate.one_mem (by
        simpa only [Nat.cast_ofNat,show (1000 : ℝ)+1 = 1001 by norm_num] using hv)
    apply p.signedProgression_mul_mem L hd hr hA.approximate.one_mem hA.approximate.inv_mem
      (hA.approximate.allProducts.mono L (Set.Subset.refl _) (by omega : 8 ≤ 200))
      1000 (by omega) (strong_local_trapping_four L hA) (by omega) hmem ?_ hx hy hmul hreturn
    intro v hvp
    have he : v = z := hvp.unique L (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hz)
    exact he.symm ▸ hzout
  · intro y hy x hx
    obtain ⟨z,hxy,hyx⟩ := hcentral x hx y hy
    exact ⟨z,hyx,hxy⟩
end DirectedCycles
