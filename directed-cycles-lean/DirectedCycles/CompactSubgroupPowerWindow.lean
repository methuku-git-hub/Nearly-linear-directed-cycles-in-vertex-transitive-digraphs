module

public import DirectedCycles.CompactTwoSidedWindow
public import DirectedCycles.ClosedWordPowers
public import Mathlib.Topology.Separation.Regular

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A compact subgroup has an open neighbourhood whose prescribed word
power lies in any specified open neighbourhood of the subgroup. -/
theorem compact_subgroup_open_word_window (N : Subgroup G)
    (hN : IsCompact (N : Set G)) {U : Set G} (hU : IsOpen U)
    (hNU : (N : Set G) ⊆ U) (n : ℕ) :
    ∃ W : Set G, IsOpen W ∧ (N : Set G) ⊆ W ∧ W^n ⊆ U := by
  induction n generalizing U with
  | zero => exact ⟨Set.univ,isOpen_univ,Set.subset_univ _,by simpa using hNU N.one_mem⟩
  | succ n ih =>
      obtain ⟨A,B,hA,hB,hNA,hNB,hAB⟩ := generalized_tube_lemma hN hN
        (hU.preimage continuous_mul) (by
          rintro ⟨a,b⟩ ⟨ha,hb⟩
          exact hNU (N.mul_mem ha hb))
      obtain ⟨W,hW,hNW,hWn⟩ := ih hA hNA
      refine ⟨W ∩ B,hW.inter hB,fun _ hx => ⟨hNW hx,hNB hx⟩,?_⟩
      rw [pow_succ]
      rintro x ⟨a,ha,b,hb,rfl⟩
      exact hAB (show (a,b) ∈ A ×ˢ B from
        ⟨hWn (Set.pow_subset_pow_left Set.inter_subset_left ha),hb.2⟩)

/-- The neighbourhood can be chosen symmetric and precompact, while
controlling the closure of its finite word power. -/
theorem compact_subgroup_closed_word_window [T2Space G] [LocallyCompactSpace G]
    (N : Subgroup G) (hN : IsCompact (N : Set G)) {U : Set G}
    (hU : IsOpen U) (hNU : (N : Set G) ⊆ U) (n : ℕ) :
    ∃ W : Set G, IsOpen W ∧ (N : Set G) ⊆ W ∧ W⁻¹ = W ∧
      IsCompact (closure W) ∧ closure (W^n) ⊆ U := by
  obtain ⟨A,hA,hNA,hAn⟩ := compact_subgroup_open_word_window N hN hU hNU n
  obtain ⟨B,hB,hNB,hBA,hBc⟩ := exists_open_between_and_isCompact_closure hN hA hNA
  let W := B ∩ B⁻¹
  have hNW : (N : Set G) ⊆ W := fun _ hx => ⟨hNB hx,hNB (N.inv_mem hx)⟩
  have hWi : W⁻¹ = W := by
    ext z
    change (z⁻¹ ∈ B ∧ (z⁻¹)⁻¹ ∈ B) ↔ (z ∈ B ∧ z⁻¹ ∈ B)
    simp only [inv_inv,and_comm]
  have hWB : closure W ⊆ closure B := closure_mono Set.inter_subset_left
  have hWc : IsCompact (closure W) := hBc.of_isClosed_subset isClosed_closure hWB
  refine ⟨W,hB.inter hB.inv,hNW,hWi,hWc,?_⟩
  refine (closure_minimal (Set.pow_subset_pow_left subset_closure)
    (compact_set_word_power hWc n).isClosed).trans ?_
  exact (Set.pow_subset_pow_left (hWB.trans hBA)).trans hAn
end DirectedCycles
