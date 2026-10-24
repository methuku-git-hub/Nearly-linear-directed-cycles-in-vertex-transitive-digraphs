import DirectedCycles.StrongLocalCentralSet
import DirectedCycles.LocalCentralQuotientData
import DirectedCycles.LocalFiniteEscapeNeighbourhoods

set_option autoImplicit false
namespace DirectedCycles

/-- A specified central locally closed finite set admits a uniformly dense
actual local quotient. Keeping the set as input lets the same progression be
used in the independently proved model-image equality. -/
theorem local_finite_central_quotient_of_set (K : ℕ) (hK : 1 ≤ K) (r : ℝ) (hr0 : 0 < r) :
    ∃ (J : ℕ) (δ : ℝ), 1 ≤ J ∧ 0 < δ ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G)
        (_hd : L.DivisionClosed) (_hr : L.Reversible) (A : Finset G),
        IsStrongLocalFiniteApproximateGroup L K A →
        ∀ P : Finset G, L.CentralLocalSet (P : Set G) {x | L.escapeNorm A x < 1/1001}
          {x | L.escapeNorm A x < r} →
          ∃ D : L.CentralQuotientData (P : Set G), ∃ B : Finset G,
            IsLocalFiniteApproximateGroup L J B ∧ δ*A.card ≤ B.card ∧
            (∀ n ≤ 200, L.wordPower (B : Set G) n ⊆ D.small) ∧
            D.small ⊆ {x | L.escapeNorm A x < r} ∧
            IsLocalFiniteApproximateGroup D.algebra J (D.finiteImage B) ∧
            D.algebra.DivisionClosed ∧ D.algebra.Reversible ∧
            δ*A.card ≤ (D.finiteImage B).card * (P.card : ℝ) := by
  let ε : ℝ := min r (1/1001)
  have hε : 0 < ε := lt_min hr0 (by norm_num)
  obtain ⟨J,δ,hJ,hδ,hsmall⟩ := local_finite_escape_neighbourhoods K hK 1000 (by omega) 4800 ε hε
  refine ⟨J,δ,hJ,hδ,?_⟩
  intro G _ L hd hr A hA P hP
  obtain ⟨B,hB,hBd,hdom,hpowers⟩ := hsmall G L hd hr A hA.approximate (strong_local_trapping_four L hA)
  let W := L.wordPower (B : Set G) 200
  let S := L.wordPower W 3
  have hWdom : L.AllProductsDefined W 24 := hdom.wordPower L (by omega : 200*24 ≤ 4800)
  have hSdom : L.AllProductsDefined S 8 := hWdom.wordPower L (by omega : 3*8 ≤ 24)
  have hW1 : L.one ∈ W :=
    ⟨List.replicate 200 L.one,List.length_replicate,by
      intro x hx
      exact (List.mem_replicate.mp hx).2.symm ▸ hB.one_mem,L.product_replicate_one 200⟩
  have hWi : ∀ x ∈ W, L.inv x ∈ W := fun _ hx => L.inv_mem_wordPower hr hB.inv_mem hx
  have hS1 : L.one ∈ S :=
    ⟨List.replicate 3 L.one,List.length_replicate,by
      intro x hx
      exact (List.mem_replicate.mp hx).2.symm ▸ hW1,L.product_replicate_one 3⟩
  have hSi : ∀ x ∈ S, L.inv x ∈ S := fun _ hx => L.inv_mem_wordPower hr hWi hx
  have hWS : W ⊆ S := by
    intro x hx
    apply L.wordPower_subset_wordPower hW1 hWdom (by omega : 1 ≤ 3) (by omega)
    simpa only [L.wordPower_one] using hx
  have hSr : S ⊆ {x | L.escapeNorm A x < r} := by
    intro x hx
    have hx' := L.wordPower_wordPower_subset hdom 200 3 (by omega) hx
    exact (hpowers 600 (by omega) x hx').trans_le (min_le_left _ _)
  have hSV : L.wordPower S 8 ⊆ {x | L.escapeNorm A x < 1/1001} := by
    intro x hx
    have hxW := L.wordPower_wordPower_subset hWdom 3 8 (by omega) hx
    have hxB := L.wordPower_wordPower_subset hdom 200 24 (by omega) hxW
    exact (hpowers 4800 le_rfl x hxB).trans_le (min_le_right _ _)
  have hP' : L.CentralLocalSet (P : Set G) {x | L.escapeNorm A x < 1/1001} S :=
    ⟨hP.one_mem,hP.inv_mem,hP.mul_mem,fun p hp x hx => hP.central p hp x (hSr hx)⟩
  let E := hP'.equivalenceWindow hd hr hS1 hSi hSdom hSV
  let D : L.CentralQuotientData (P : Set G) := {
    large := S
    small := W
    small_subset := hWS
    one_mem := hW1
    inv_mem := hWi
    domain := hWdom.mono L (Set.Subset.refl _) (by omega : 3 ≤ 24)
    cube_subset := Set.Subset.refl _
    equivalence := E
    relation_iff := fun _ _ => Iff.rfl }
  have hBsmall : ∀ n ≤ 200, L.wordPower (B : Set G) n ⊆ D.small := by
    intro n hn
    exact L.wordPower_subset_wordPower hB.one_mem hdom hn (by omega)
  have hBW : (B : Set G) ⊆ D.small := by
    simpa only [L.wordPower_one] using hBsmall 1 (by omega)
  have hcard := D.finiteImage_card_bound (LocalGroupAlgebra.DivisionClosed.cancellative L hd hr) B P hBW (Set.Subset.refl _)
  have hcardR : (B.card : ℝ) ≤ (D.finiteImage B).card * (P.card : ℝ) := by
    exact_mod_cast hcard
  have hDsmall : D.small ⊆ {x | L.escapeNorm A x < r} := by
    intro x hx
    exact (hpowers 200 (by omega) x hx).trans_le (min_le_left _ _)
  exact ⟨D,B,hB,hBd,hBsmall,hDsmall,D.finiteImage_approximate hB hBsmall,
    D.algebra_divisionClosed hd,D.algebra_reversible hr,hBd.trans hcardR⟩
end DirectedCycles
