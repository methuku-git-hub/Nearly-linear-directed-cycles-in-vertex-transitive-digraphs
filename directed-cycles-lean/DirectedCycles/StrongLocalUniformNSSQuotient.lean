module

public import DirectedCycles.StrongLocalApproximateGroups
public import DirectedCycles.LocalFiniteEscapeNeighbourhoods

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem strong_local_trapping_four {K : ℕ} {A : Finset G}
    (hA : IsStrongLocalFiniteApproximateGroup L K A) :
    ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 →
      L.PowerIn (L.wordPower (A : Set G) 4) x j) → x ∈ A := by
  obtain ⟨S,_,_,_,hfirst,_⟩ := hA.trapping
  intro x hx
  apply hfirst x
  intro j hj hj'
  obtain ⟨y,hy,hp⟩ := hx j hj hj'
  exact ⟨y,L.wordPower_subset_wordPower hA.approximate.one_mem hA.approximate.allProducts
    (by norm_num : 4 ≤ 100) (by norm_num) hy,hp⟩

/-- Every finite strong local approximate group has a uniformly dense small
approximate neighbourhood and an actual NSS local quotient of it. This
removes the extra small-neighbourhood premise from the finite local caller.
The cardinality loss is exactly the proved zero-escape fibre bound. -/
theorem strong_local_uniform_nss_quotient (K : ℕ) (hK : 1 ≤ K) :
    ∃ (J : ℕ) (δ : ℝ), 1 ≤ J ∧ 0 < δ ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G)
        (hd : L.DivisionClosed) (hr : L.Reversible) (A : Finset G),
      IsStrongLocalFiniteApproximateGroup L K A →
      let H := {x | L.escapeNorm A x = 0}
      ∃ B : Finset G, IsLocalFiniteApproximateGroup L J B ∧
        δ*A.card ≤ B.card ∧ L.wordPower (B : Set G) 200 ⊆ (A : Set G) ∧
        ∃ W : L.NormalSubgroupWindow H (L.setMul H A),
          IsLocalFiniteApproximateGroup (W.congruence hd hr).algebra J (W.finiteImage hd hr B) ∧
          (W.congruence hd hr).algebra.IsNSS Set.univ ∧
          (W.congruence hd hr).algebra.DivisionClosed ∧
          (W.congruence hd hr).algebra.Reversible ∧
          δ*A.card ≤ (W.finiteImage hd hr B).card*((localZeroEscapeFinset L A).card : ℝ) := by
  obtain ⟨J,δ,hJ,hδ,hsmall⟩ := local_finite_trapped_neighbourhoods K hK 1000 (by norm_num) 200
  refine ⟨J,δ,hJ,hδ,?_⟩
  intro G _ L hd hr A hA
  dsimp only
  obtain ⟨B,hB,hBd,_,hBA⟩ := hsmall G L hd hr A hA.approximate (strong_local_trapping_four L hA)
  have hsmallB := hBA 200 le_rfl
  obtain ⟨W,hQ,hNSS,hD,hR,hcard⟩ := strong_local_nss_approximate_quotient L hd hr hA hB hsmallB
  exact ⟨B,hB,hBd,hsmallB,W,hQ,hNSS,hD,hR,hBd.trans (by exact_mod_cast hcard)⟩
end DirectedCycles
