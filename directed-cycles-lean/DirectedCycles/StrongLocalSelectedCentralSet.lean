import DirectedCycles.StrongLocalCentralSet
import DirectedCycles.LocalSelectedProgression

set_option autoImplicit false
namespace DirectedCycles

/-- The central locally closed set can be built from a specified first-exit
segment. This keeps the finite quotient and the model curve attached to the
same generator, rather than choosing unrelated existence witnesses. -/
theorem strong_local_central_set_of_segment {G : Type*} (L : LocalGroupAlgebra G)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A)
    (hd : L.DivisionClosed) (hr : L.Reversible) (hNSS : L.IsNSS (A : Set G))
    {u : G} (hu : u ∈ A) (hu1 : u ≠ L.one) {N : ℕ} (hN : 2 ≤ N)
    (p : L.PowerSegment u (2*N)) (hprev : ∀ n < N, p.power n ∈ A)
    (hexit : p.power N ∉ A) {δ : ℝ} (hδhalf : δ ≤ 1/2)
    (hcentral : ∀ x, L.escapeNorm A x < δ → L.Commute x u) :
    ∃ P : Finset G, (P : Set G) = p.shortSignedSet N ∧ P.card = 2*N-1 ∧ (P : Set G) ⊆ A ∧
      L.CentralLocalSet (P : Set G) {x | L.escapeNorm A x < 1/1001}
        {x | L.escapeNorm A x < δ} := by
  let q : L.PowerSegment u (N-1) := ⟨p.power,fun n hn => p.product n (by omega)⟩
  have hqmem : ∀ n ≤ N-1, q.power n ∈ (A : Set G) := fun n hn => hprev n (by omega)
  have htrap : ∀ S : Set G, L.IsGlobalSubgroup S → S ⊆ L.wordPower (A : Set G) 2 → S ⊆ A := by
    intro S hS hSA
    apply strong_local_subgroup_trapping L hA S hS
    exact hSA.trans (L.wordPower_subset_wordPower hA.approximate.one_mem hA.approximate.allProducts
      (by omega : 2 ≤ 100) (by omega))
  have hinj := q.signedMap_injective L (LocalGroupAlgebra.DivisionClosed.cancellative L hd hr)
    hA.approximate.one_mem hNSS htrap hu1 (by omega) hqmem
    (hA.approximate.allProducts.mono L (Set.Subset.refl _) (by omega : 8 ≤ 200))
  refine ⟨q.signedProgression L,p.prefix_signedProgression_eq L q (by omega) (fun _ _ => rfl),?_,
    q.signedProgression_subset L hA.approximate.inv_mem hqmem,?_⟩
  · rw [q.card_signedProgression L hinj]
    omega
  · refine ⟨q.one_mem_signedProgression L,fun _ hy => q.inv_mem_signedProgression L hy,?_,?_⟩
    · intro x hx y hy v hv hmul
      change L.escapeNorm A v < 1/1001 at hv
      have hreturn : ∀ j ≤ 1000, L.PowerIn (A : Set G) v j :=
        L.powerIn_of_escapeNorm_lt hA.approximate.one_mem (by
          simpa only [Nat.cast_ofNat,show (1000 : ℝ)+1 = 1001 by norm_num] using hv)
      apply q.signedProgression_mul_mem L hd hr hA.approximate.one_mem hA.approximate.inv_mem
        (hA.approximate.allProducts.mono L (Set.Subset.refl _) (by omega : 8 ≤ 200))
        1000 (by omega) (strong_local_trapping_four L hA) (by omega) hqmem ?_ hx hy hmul hreturn
      intro z hz
      have he : z = p.power N := hz.unique L (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using p.product N (by omega))
      exact he.symm ▸ hexit
    · intro y hy x hx
      have hxA : x ∈ (A : Set G) := L.mem_of_escapeNorm_lt_one hA.approximate.one_mem (by
        change L.escapeNorm A x < δ at hx
        linarith)
      exact (q.commute_signedProgression L hd hA.approximate.inv_mem
        (hA.approximate.allProducts.mono L (Set.Subset.refl _) (by omega : 3 ≤ 200))
        hu hxA (hcentral x hx) hqmem y hy).symm L
end DirectedCycles
