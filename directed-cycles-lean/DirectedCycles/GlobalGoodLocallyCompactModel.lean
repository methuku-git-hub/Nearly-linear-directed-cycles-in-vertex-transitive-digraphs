import DirectedCycles.InternalLocallyCompactTopology
import DirectedCycles.InternalGoodModel

set_option autoImplicit false
open Filter
open scoped Pointwise Topology
namespace DirectedCycles

/-- Global BGT 6.10 for an actual sequence of finite approximate groups:
a genuine Hausdorff metrizable locally compact good model of the internal
fourth power, including approximation between compact and open preimages. -/
theorem exists_global_good_locallyCompact_model (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Finset (G i)) (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
    let H := Subgroup.closure B
    Nonempty (InternalLocallyCompactGroupModel H (H.subtype ⁻¹' (B^4)) (IsInternalFiniteIn u G H)) := by
  classical
  obtain ⟨C⟩ := exists_approximate_root_chain G A K hK hA
  let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
  let H := Subgroup.closure B
  let S := C.shrinking (u : Filter ℕ) (fun i => (hA i).one_mem)
  let basis := C.modelBasis u (fun i => (hA i).one_mem) (fun i => (hA i).inv_eq_self)
  let : TopologicalSpace H := basis.topology
  let : IsTopologicalGroup H := basis.isTopologicalGroup
  have hc : IsCompact (H.subtype ⁻¹' (B^4)) := C.compact_fourth_power u hu K hA
  have hn : H.subtype ⁻¹' (B^4) ∈ 𝓝 (1 : H) := by
    have hs : H.subtype ⁻¹' S.sets 0 ∈ 𝓝 (1 : H) := basis.mem_nhds_one ⟨0,rfl⟩
    exact Filter.mem_of_superset hs (fun x hx =>
      C.shrinking_subset (u : Filter ℕ) (fun i => (hA i).one_mem) 0 hx)
  apply exists_internal_separated_model u G H (H.subtype ⁻¹' (B^4)) hc hn
    (fun n => H.subtype ⁻¹' S.sets n)
    (S.subgroup_nhds_basis H (C.shrinking_conjugation u (fun i => (hA i).one_mem)
      (fun i => (hA i).inv_eq_self)))
  intro n
  refine ⟨fun i => (C.roots n i)^4,?_⟩
  simp only [Finset.coe_pow,ultraSet_pow]
  rfl

/-- The representative sets in the good-model sandwich can be chosen
literally inside the corresponding finite fourth powers. -/
theorem global_good_model_component_sandwich (u : Ultrafilter ℕ)
    (G : ℕ → Type*) [∀ i, Group (G i)] [∀ i, DecidableEq (G i)]
    (A : ∀ i, Finset (G i))
    (M : let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
      let H := Subgroup.closure B
      InternalLocallyCompactGroupModel H (H.subtype ⁻¹' (B^4)) (IsInternalFiniteIn u G H))
    (F U : Set M.carrier) (hF : @IsCompact M.carrier M.topology F)
    (hU : @IsOpen M.carrier M.topology U) (hFU : F ⊆ U) (hUU : U ⊆ M.neighbourhood) :
    ∃ D : ∀ i, Finset (G i), (∀ i, D i ⊆ (A i)^4) ∧
      M.map ⁻¹' F ⊆ (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))).subtype ⁻¹'
        ultraSet (u : Filter ℕ) G (fun i => (D i : Set (G i))) ∧
      (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))).subtype ⁻¹'
        ultraSet (u : Filter ℕ) G (fun i => (D i : Set (G i))) ⊆ M.map ⁻¹' U := by
  obtain ⟨D,hD,hFD,hDU⟩ := M.internal_sandwich F U hF hU hFU hUU
  have hDA := hDU.trans ((Set.preimage_mono hUU).trans M.small_neighbourhood)
  obtain ⟨E,hEA,hE⟩ := hD.restrict (fun i => (A i)^4) (by
    simpa only [Finset.coe_pow,ultraSet_pow] using hDA)
  exact ⟨E,hEA,hE ▸ hFD,hE ▸ hDU⟩

end DirectedCycles
