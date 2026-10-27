module

public import DirectedCycles.TrappingExitSelection
public import DirectedCycles.CompactKernelCyclicWindow

@[expose] public section

set_option autoImplicit false
open TopologicalSpace Filter
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]

/-- The compact-limit argument rules out a family of first word exits
whose generators have uniformly small entire cyclic orbits. The second
exit limit lies in the compact limiting subgroup and is forced into its
small kernel, contradicting its location outside the kernel window. -/
theorem no_shrinking_word_exit_family {ι : Type*} (u : Ultrafilter ι)
    {U : Set G} (hU : IsOpen U) (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U)
    (hUc : IsCompact (closure U)) (Q : ι → Set G) (r : ι → ℕ)
    (hQ1 : ∀ i, (1 : G) ∈ Q i) (hQi : ∀ i, (Q i)⁻¹ = Q i)
    (hr : ∀ i, 0 < r i) (hQr : ∀ i, (Q i)^(r i) ⊆ U)
    (hsmall : ∀ V : Set G, IsOpen V → (1 : G) ∈ V →
      ∀ᶠ i in (u : Filter ι), ∀ q ∈ Q i, ∀ j : ℕ, q^j ∈ V)
    (hfail : ∀ᶠ i in (u : Filter ι), ¬ (Subgroup.closure (Q i) : Set G) ⊆ U)
    (hrmax : ∀ᶠ i in (u : Filter ι), ∀ k : ℕ, (Q i)^k ⊆ U → k ≤ r i) : False := by
  obtain ⟨E,_hE1,_hEi,_hEU,hElim,hHc,_hHU⟩ :=
    trapping_limit_subgroup u hU hU1 hUi hUc Q r hQ1 hQi hr hQr hsmall
  let H := Subgroup.topologicalClosure (Subgroup.closure (E : Set G))
  let : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  obtain ⟨N,hNnormal,hNc,hNU,hnss⟩ := compact_nss_approximation H
    (H.subtype ⁻¹' U) (hU.preimage continuous_subtype_val) hU1
  let := hNnormal
  have hNamb : (N.map H.subtype : Set G) ⊆ U := by
    rintro z ⟨x,hx,rfl⟩
    exact hNU hx
  obtain ⟨O,hO,hO1,hOi,hOc,hNO,hOU,hcyclic⟩ :=
    compact_kernel_cyclic_window H hHc N hNc hnss hU hNamb
  obtain ⟨s,g,hsg⟩ := smaller_word_exit_selection Q r hO hO1 hOU hQ1 hQi hsmall hfail hrmax
  let A := fun i => closedWordWindow hUc (Q i) (r i) (hQr i)
  have hgA : ∀ᶠ i in (u : Filter ι), g i ∈ compactWindowPower (A i) 2 := by
    filter_upwards [hsg] with i hi
    rw [← SetLike.mem_coe,compactWindowPower_coe]
    change g i ∈ (closure ((Q i)^(r i)))^2
    apply Set.pow_subset_pow_left subset_closure
    rw [← pow_mul]
    exact Set.pow_subset_pow_right (hQ1 i) (by have := hr i; omega) hi.2.2.2.1
  have hgK : ∀ᶠ i in (u : Filter ι), g i ∈ (closure U)^2 := by
    filter_upwards [hgA] with i hi
    rw [← SetLike.mem_coe,compactWindowPower_coe] at hi
    exact Set.pow_subset_pow_left (closure_mono (hQr i)) hi
  obtain ⟨x,_hxK,hxlim⟩ := (compact_set_word_power hUc 2).ultrafilter_le_nhds' (u.map g) hgK
  have hxlim' : Tendsto g (u : Filter ι) (𝓝 x) := hxlim
  have hxE : x ∈ compactWindowPower E 2 :=
    compact_limit_varying_mem (compact_window_power_tendsto hElim 2) hxlim hgA
  have hxH : x ∈ H := by
    rw [← SetLike.mem_coe,compactWindowPower_coe,pow_two] at hxE
    obtain ⟨a,ha,b,hb,rfl⟩ := hxE
    exact H.mul_mem ((Subgroup.closure (E : Set G)).le_topologicalClosure
      (Subgroup.subset_closure ha)) ((Subgroup.closure (E : Set G)).le_topologicalClosure
      (Subgroup.subset_closure hb))
  have hxnot : x ∉ O := hO.isClosed_compl.mem_of_tendsto hxlim
    (hsg.mono (fun _ hi => hi.2.2.2.2))
  have hxpow : ∀ j : ℕ, x^j ∈ closure (O^4) := by
    intro j
    obtain ⟨V,hV,hV1,_hVi,htrap⟩ := locally_compact_finite_trapping hO hO1 hOi hOc (2*j)
    apply isClosed_closure.mem_of_tendsto (hxlim'.pow j)
    filter_upwards [hsg,hsmall V hV hV1] with i hi hci
    apply subset_closure
    apply htrap (Q i) (hQ1 i) (hQi i) hci (s i) hi.1 hi.2.2.1
    have hp : (g i)^j ∈ ((Q i)^(s i+1))^j := Set.pow_mem_pow hi.2.2.2.1
    rw [← pow_mul] at hp
    exact Set.pow_subset_pow_right (hQ1 i) (by nlinarith [hi.1]) hp
  have hxN : (⟨x,hxH⟩ : H) ∈ N := hcyclic ⟨x,hxH⟩ hxpow
  exact hxnot (hNO (Subgroup.mem_map.mpr ⟨⟨x,hxH⟩,hxN,rfl⟩))
end DirectedCycles
