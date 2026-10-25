module

public import DirectedCycles.StrongLocalCentralElement
public import DirectedCycles.LocalCommutingPowers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Strong-group trapping forces every genuine global subgroup of A^100
into A, including all its elements and all powers. -/
theorem strong_local_subgroup_trapping {K : ℕ} {A : Finset G}
    (hA : IsStrongLocalFiniteApproximateGroup L K A) (H : Set G)
    (hH : L.IsGlobalSubgroup H) (hHA : H ⊆ L.wordPower (A : Set G) 100) : H ⊆ A := by
  obtain ⟨S,_,_,_,hfirst,_⟩ := hA.trapping
  intro x hx
  apply hfirst x
  intro j _ _
  obtain ⟨y,hy,hp⟩ := hH.powerIn hx j
  exact ⟨y,hHA hy,hp⟩

/-- The central signed progression in a finite strong local NSS approximate
group has its exact cardinality, all product domains, and a uniform
centralizing neighbourhood proved from the strong-group hypotheses. -/
theorem strong_local_central_progression (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G) (A : Finset G),
        IsStrongLocalFiniteApproximateGroup L K A → L.DivisionClosed → L.Reversible →
        L.IsNSS (A : Set G) → (∃ g ∈ A, g ≠ L.one) →
        ∃ u ∈ A, u ≠ L.one ∧ ∃ N : ℕ, 2 ≤ N ∧ ∃ p : L.PowerSegment u (N-1),
          (∀ n ≤ N-1, p.power n ∈ A) ∧
          (∃ z, L.Product (List.replicate N u) z ∧ z ∉ A) ∧
          L.escapeNorm A u = 1/(N : ℝ) ∧
          (p.signedProgression L).card = 2*N-1 ∧
          (p.signedProgression L : Set G) ⊆ A ∧
          L.one ∈ p.signedProgression L ∧
          (∀ y ∈ p.signedProgression L, L.inv y ∈ p.signedProgression L) ∧
          (∀ x, L.escapeNorm A x < δ → ∀ y ∈ p.signedProgression L, L.Commute x y) := by
  obtain ⟨δ,hδ,hδhalf,hcent⟩ := strong_local_central_element K
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro G _ L A hA hd hr hNSS hne
  obtain ⟨u,hu,hu1,hupos,_,hcentral,_⟩ := hcent G L A hA hd hr hNSS hne
  obtain ⟨N,hN,p,hout,hmem,_,hnorm⟩ := L.exists_first_exit_segment hA.approximate.one_mem hu
    (hA.approximate.allProducts.mono L (Set.Subset.refl _) (by omega : 2 ≤ 200)) hupos
  have hN2 : 2 ≤ N := by
    by_contra h
    have he : N = 1 := by omega
    have hp1 := p.one (by omega)
    have hpN : p.power N = u := by simpa only [he] using hp1
    exact hout (hpN.symm ▸ hu)
  let q : L.PowerSegment u (N-1) := ⟨p.power,fun n hn => p.product n (by omega)⟩
  have hqmem : ∀ n ≤ N-1, q.power n ∈ (A : Set G) := fun n hn => hmem n (by omega)
  have htrap : ∀ H : Set G, L.IsGlobalSubgroup H → H ⊆ L.wordPower (A : Set G) 2 → H ⊆ A := by
    intro H hH hHA
    apply strong_local_subgroup_trapping L hA H hH
    exact hHA.trans (L.wordPower_subset_wordPower hA.approximate.one_mem hA.approximate.allProducts
      (by omega : 2 ≤ 100) (by omega))
  have hinj := q.signedMap_injective L (LocalGroupAlgebra.DivisionClosed.cancellative L hd hr)
    hA.approximate.one_mem hNSS htrap hu1 (by omega) hqmem
    (hA.approximate.allProducts.mono L (Set.Subset.refl _) (by omega : 8 ≤ 200))
  refine ⟨u,hu,hu1,N,hN2,q,hqmem,⟨p.power N,p.product N le_rfl,hout⟩,hnorm,?_,
    q.signedProgression_subset L hA.approximate.inv_mem hqmem,q.one_mem_signedProgression L,
    fun _ hy => q.inv_mem_signedProgression L hy,?_⟩
  · rw [q.card_signedProgression L hinj]
    omega
  · intro x hx
    have hxA : x ∈ (A : Set G) := L.mem_of_escapeNorm_lt_one hA.approximate.one_mem (by linarith)
    exact q.commute_signedProgression L hd hA.approximate.inv_mem
      (hA.approximate.allProducts.mono L (Set.Subset.refl _) (by omega : 3 ≤ 200)) hu hxA (hcentral x hx) hqmem
end DirectedCycles
