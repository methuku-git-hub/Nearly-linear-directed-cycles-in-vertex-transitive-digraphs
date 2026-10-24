import DirectedCycles.GlobalGoodModelSymmetricSandwich
import DirectedCycles.GlobalGoodLieModelExistence
import DirectedCycles.CompactSubgroupPowerWindow
import DirectedCycles.InternalFiniteCoverTransfer

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Pointwise Topology
namespace DirectedCycles

/-- Concrete finite windows around the compact kernel in the initial good
model. The larger window contains every product of two elements of the
smaller window on a large set of indices. Both are actual internal sets. -/
structure GlobalGoodModelKernelWindows (u : Ultrafilter ℕ)
    (G : ℕ → Type*) [∀ i, Group (G i)] [∀ i, DecidableEq (G i)] (A : ∀ i, Finset (G i))
    (M : let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
      let H := Subgroup.closure B
      InternalLocallyCompactGroupModel H (H.subtype ⁻¹' (B^4)) (IsInternalFiniteIn u G H))
    (D : LieQuotientData M.carrier M.neighbourhood) where
  inner : Set M.carrier
  outer : Set M.carrier
  inner_open : IsOpen inner
  inner_one : (1 : M.carrier) ∈ inner
  kernel_inner : (D.kernel.map D.source.subtype : Set M.carrier) ⊆ inner
  inner_outer : closure inner ⊆ outer
  outer_open : IsOpen outer
  W : ∀ i, Finset (G i)
  B : ∀ i, Finset (G i)
  W_data : ∀ i, (1 : G i) ∈ W i ∧ (∀ x ∈ W i, x⁻¹ ∈ W i) ∧ W i ⊆ (A i)^4
  B_data : ∀ i, (1 : G i) ∈ B i ∧ (∀ x ∈ B i, x⁻¹ ∈ B i) ∧ B i ⊆ (A i)^4
  W_lower : M.map ⁻¹' closure (outer^2) ⊆
    (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))).subtype ⁻¹'
      ultraSet (u : Filter ℕ) G (fun i => (W i : Set (G i)))
  W_source : (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))).subtype ⁻¹'
    ultraSet (u : Filter ℕ) G (fun i => (W i : Set (G i))) ⊆ M.map ⁻¹' (D.source : Set M.carrier)
  B_lower : M.map ⁻¹' closure inner ⊆
    (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))).subtype ⁻¹'
      ultraSet (u : Filter ℕ) G (fun i => (B i : Set (G i)))
  B_upper : (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))).subtype ⁻¹'
    ultraSet (u : Filter ℕ) G (fun i => (B i : Set (G i))) ⊆ M.map ⁻¹' outer
  products : ∀ᶠ i in (u : Filter ℕ), (B i : Set (G i))^2 ⊆ (W i : Set (G i))
  density : ∃ J : ℕ, 1 ≤ J ∧ ∀ᶠ i in (u : Filter ℕ), (A i).card ≤ J*(B i).card

/-- Construct the finite domain windows using compact kernel neighbourhoods
and the original absolute internal sandwich, before restricting the source
of the Lie quotient. No arbitrary subgroup is asserted to be internal. -/
theorem global_good_model_kernel_windows (u : Ultrafilter ℕ)
    (G : ℕ → Type*) [∀ i, Group (G i)] [∀ i, DecidableEq (G i)]
    (A : ∀ i, Finset (G i)) (hA1 : ∀ i, (1 : G i) ∈ A i)
    (M : let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
      let H := Subgroup.closure B
      InternalLocallyCompactGroupModel H (H.subtype ⁻¹' (B^4)) (IsInternalFiniteIn u G H))
    (D : LieQuotientData M.carrier M.neighbourhood) :
    Nonempty (GlobalGoodModelKernelWindows u G A M D) := by
  classical
  let N := D.kernel.map D.source.subtype
  have hNc : IsCompact (N : Set M.carrier) := D.compact_kernel.image continuous_subtype_val
  let V := M.neighbourhood ∩ (D.source : Set M.carrier)
  have hVo : IsOpen V := M.open_neighbourhood.inter D.source_open
  have hNV : (N : Set M.carrier) ⊆ V := by
    rintro x ⟨y,hy,rfl⟩
    exact ⟨D.kernel_small hy,y.property⟩
  obtain ⟨O,hOo,hNO,hOi,hOc,hO2⟩ := compact_subgroup_closed_word_window N hNc hVo hNV 2
  have hO1 : (1 : M.carrier) ∈ O := hNO N.one_mem
  have hOV : O ⊆ V := by
    intro x hx
    apply hO2
    apply subset_closure
    exact Set.subset_pow hO1 (by omega : 2 ≠ 0) hx
  obtain ⟨I,hIo,hNI,hIi,hIc,hI1⟩ := compact_subgroup_closed_word_window N hNc hOo hNO 1
  have hIO : closure I ⊆ O := by simpa only [pow_one] using hI1
  have hIone : (1 : M.carrier) ∈ I := hNI N.one_mem
  have hF2i := symmetric_closure_word_power hOi 2
  obtain ⟨W,hW,hWlo,hWup⟩ := global_good_model_symmetric_sandwich u G A hA1 M
    (closure (O^2)) V (compact_closure_word_power hOc 2) hVo hO2 Set.inter_subset_left
    (subset_closure (Set.one_mem_pow hO1)) (by
      intro x hx
      have hh := Set.inv_mem_inv.mpr hx
      simpa only [hF2i] using hh)
  obtain ⟨B,hB,hBlo,hBup⟩ := global_good_model_symmetric_sandwich u G A hA1 M
    (closure I) O hIc hOo hIO (hOV.trans Set.inter_subset_left)
    (subset_closure hIone) (by
      intro x hx
      have hh := Set.inv_mem_inv.mpr hx
      simpa only [inv_closure,hIi] using hh)
  let T := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
  let H := Subgroup.closure T
  let BS := ultraSet (u : Filter ℕ) G (fun i => (B i : Set (G i)))
  let WS := ultraSet (u : Filter ℕ) G (fun i => (W i : Set (G i)))
  have hB4 : BS ⊆ T^4 := by
    dsimp only [BS,T]
    rw [← ultraSet_pow]
    exact ultraSet_mono (u : Filter ℕ) G _ _
      (Filter.Eventually.of_forall fun i => by
        rw [← Finset.coe_pow]
        exact (hB i).2.2)
  have hTH : T^4 ⊆ (H : Set _) := by
    intro x hx
    obtain ⟨l,_hlen,hl,he⟩ := exists_list_of_mem_set_power hx
    rw [← he]
    exact H.list_prod_mem (fun y hy => Subgroup.subset_closure (hl y hy))
  have hBH : BS ⊆ (H : Set _) := hB4.trans hTH
  have hprod : BS^2 ⊆ WS := by
    rw [pow_two]
    rintro x ⟨a,ha,b,hb,rfl⟩
    let a' : H := ⟨a,hBH ha⟩
    let b' : H := ⟨b,hBH hb⟩
    have ham : M.map a' ∈ O := hBup ha
    have hbm : M.map b' ∈ O := hBup hb
    have hm : M.map (a'*b') ∈ closure (O^2) := by
      rw [map_mul,pow_two]
      exact subset_closure (Set.mul_mem_mul ham hbm)
    exact hWlo hm
  have hcomponents : ∀ᶠ i in (u : Filter ℕ), (B i : Set (G i))^2 ⊆ (W i : Set (G i)) := by
    apply (ultraSet_subset_iff_eventually u G _ _).1
    rw [ultraSet_pow]
    exact hprod
  obtain ⟨F,hF⟩ := good_model_finite_cover M (H.subtype ⁻¹' BS) I hIo hIone
    (fun _ hx => hBlo (subset_closure hx))
  let F' : Finset (GroupUltraproduct (u : Filter ℕ) G) := F.image H.subtype
  have hcover : T ⊆ (F' : Set _)*BS := by
    intro x hx
    let x' : H := ⟨x,Subgroup.subset_closure hx⟩
    have hxT : x' ∈ H.subtype ⁻¹' (T^4) := Set.subset_pow
      ((ultraMk_mem_ultraSet_iff (u : Filter ℕ) G _ 1).2 (Filter.Eventually.of_forall hA1))
      (by omega : 4 ≠ 0) hx
    obtain ⟨a,ha,b,hb,he⟩ := hF hxT
    refine ⟨a.val,Finset.mem_image.mpr ⟨a,ha,rfl⟩,b.val,hb,?_⟩
    exact congrArg Subtype.val he
  obtain ⟨C,hC,hcov⟩ := finite_cover_components u G (fun i => (A i : Set (G i)))
    (fun i => (B i : Set (G i))) F' hcover
  have hdensity : ∀ᶠ i in (u : Filter ℕ), (A i).card ≤ (F'.card+1)*(B i).card := by
    filter_upwards [hcov] with i hi
    have hsub : A i ⊆ C i * B i := by simpa only [← Finset.coe_mul,Finset.coe_subset] using hi
    exact ((Finset.card_le_card hsub).trans Finset.card_mul_le).trans
      (Nat.mul_le_mul_right _ (by have := hC i; omega))
  exact ⟨{
    inner := I
    outer := O
    inner_open := hIo
    inner_one := hIone
    kernel_inner := hNI
    inner_outer := hIO
    outer_open := hOo
    W := W
    B := B
    W_data := hW
    B_data := hB
    W_lower := hWlo
    W_source := fun _ hx => (hWup hx).2
    B_lower := hBlo
    B_upper := hBup
    products := hcomponents
    density := ⟨F'.card+1,by omega,hdensity⟩ }⟩
end DirectedCycles
