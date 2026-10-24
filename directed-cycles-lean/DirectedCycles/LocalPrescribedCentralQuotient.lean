import DirectedCycles.StrongLocalCentralSet
import DirectedCycles.LocalCentralQuotientData
import DirectedCycles.LocalFiniteEscapeNeighbourhoods

set_option autoImplicit false
namespace DirectedCycles

/-- Construct the actual central quotient from a prescribed small word
window. This permits the window to be the same exponential neighbourhood
used by escape-controlled lifting, rather than an unrelated dense subset. -/
theorem local_central_quotient_of_prescribed_window {G : Type*} [Fintype G]
    (L : LocalGroupAlgebra G) (hd : L.DivisionClosed) (hr : L.Reversible)
    (A P B : Finset G) {J : ℕ} (hB : IsLocalFiniteApproximateGroup L J B) {r : ℝ}
    (hP : L.CentralLocalSet (P : Set G) {x | L.escapeNorm A x < 1/1001}
      {x | L.escapeNorm A x < r})
    (hdom : L.AllProductsDefined (B : Set G) 4800)
    (hpowers : ∀ n ≤ 4800, ∀ x ∈ L.wordPower (B : Set G) n, L.escapeNorm (A : Set G) x < min r (1/1001)) :
    ∃ D : L.CentralQuotientData (P : Set G),
      D.small = L.wordPower (B : Set G) 200 ∧
      (∀ n ≤ 200, L.wordPower (B : Set G) n ⊆ D.small) ∧
      D.small ⊆ {x | L.escapeNorm A x < r} ∧
      IsLocalFiniteApproximateGroup D.algebra J (D.finiteImage B) ∧
      D.algebra.DivisionClosed ∧ D.algebra.Reversible ∧
      B.card ≤ (D.finiteImage B).card * P.card := by
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
  have hDsmall : D.small ⊆ {x | L.escapeNorm A x < r} := by
    intro x hx
    exact (hpowers 200 (by omega) x hx).trans_le (min_le_left _ _)
  exact ⟨D,rfl,hBsmall,hDsmall,D.finiteImage_approximate hB hBsmall,
    D.algebra_divisionClosed hd,D.algebra_reversible hr,hcard⟩
end DirectedCycles
