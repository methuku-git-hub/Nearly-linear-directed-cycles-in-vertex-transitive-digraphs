module

public import DirectedCycles.LocalTranslateEnergy
public import DirectedCycles.ExpansionMinimizers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

theorem finsetMul_mono {A B C D : Finset G} (hAC : A ⊆ C) (hBD : B ⊆ D) :
    L.finsetMul A B ⊆ L.finsetMul C D := by
  intro x hx
  obtain ⟨a,ha,b,hb,hm⟩ := (L.mem_finsetMul A B x).1 hx
  exact (L.mem_finsetMul C D x).2 ⟨a,hAC ha,b,hBD hb,hm⟩

theorem finsetMul_card_lower (hc : L.Cancellative) (A B : Finset G) (hB : B.Nonempty)
    (hdom : ∀ a ∈ A, ∀ b ∈ B, L.Defined a b) : A.card ≤ (L.finsetMul A B).card := by
  obtain ⟨b,hb⟩ := hB
  rw [← L.card_rightTranslate hc A b (fun a ha => hdom a ha b hb)]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨a,ha,hm⟩ := (L.mem_rightTranslate A b x).1 hx
  exact (L.mem_finsetMul A B x).2 ⟨a,ha,b,hb,hm⟩

theorem exists_local_expansion_minimizer (A : Finset G) (t : ℝ) (ht : t ≤ 1) :
    ∃ B : Finset G, B ⊆ A ∧ t*A.card ≤ B.card ∧
      ∀ C : Finset G, C ⊆ A → t*A.card ≤ C.card →
        (L.finsetMul A B).card ≤ (L.finsetMul A C).card := by
  classical
  let F := {B ∈ A.powerset | t*A.card ≤ (B.card : ℝ)}
  have hFA : A ∈ F := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),by nlinarith [Nat.cast_nonneg (α := ℝ) A.card]⟩
  obtain ⟨B,hB,hmin⟩ := F.exists_min_image (fun B => (L.finsetMul A B).card) ⟨A,hFA⟩
  obtain ⟨hBA,hBt⟩ := Finset.mem_filter.mp hB
  refine ⟨B,Finset.mem_powerset.mp hBA,hBt,?_⟩
  intro C hCA hCt
  exact hmin C (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hCA,hCt⟩)
end LocalGroupAlgebra

open FiniteAlmostPeriods in
/-- Uniform scale selection in a finite local ambient group. The scalar
plateau argument is independent of any group structure. Actual right
translations give the lower cardinal bound; the local cover gives the upper. -/
theorem local_uniform_expansion_scale (K : ℕ) (hK : 1 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G),
      L.Cancellative → ∀ A : Finset G, IsLocalFiniteApproximateGroup L K A →
      ∃ (t δ : ℝ) (B : Finset G),
        0 < t ∧ t ≤ 1 ∧ δ = t^2/(2*(K : ℝ)) ∧ δ₀ ≤ δ ∧
        B ⊆ A ∧ t*A.card ≤ B.card ∧
        ∀ C : Finset G, C ⊆ A → δ*A.card ≤ C.card →
          (1-ε)*(L.finsetMul A B).card ≤ (L.finsetMul A C).card := by
  classical
  have hKr : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  let N := ⌈(K : ℝ)/ε⌉₊
  have hN : (K : ℝ) ≤ N*ε := (div_le_iff₀ hε).mp (Nat.le_ceil ((K : ℝ)/ε))
  refine ⟨densityScale (K : ℝ) N,(densityScale_pos_le_one (K : ℝ) hKr N).1,?_⟩
  intro G _ L hc A hA
  have hcA : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA.one_mem⟩
  have hex : ∀ j : ℕ, ∃ B : Finset G, B ⊆ A ∧ densityScale (K : ℝ) j*A.card ≤ B.card ∧
      ∀ C : Finset G, C ⊆ A → densityScale (K : ℝ) j*A.card ≤ C.card →
        (L.finsetMul A B).card ≤ (L.finsetMul A C).card := fun j =>
      L.exists_local_expansion_minimizer A (densityScale (K : ℝ) j) (densityScale_pos_le_one (K : ℝ) hKr j).2
  choose B hBA hBsize hmin using hex
  let f := fun j => ((L.finsetMul A (B j)).card : ℝ)/A.card
  have hbound : ∀ j ≤ N, 1 ≤ f j ∧ f j ≤ K := by
    intro j _
    have hnon : (B j).Nonempty := Finset.card_pos.mp (by
      have hh := mul_pos (densityScale_pos_le_one (K : ℝ) hKr j).1 hcA
      have hh' : (0 : ℝ) < (B j).card := hh.trans_le (hBsize j)
      exact_mod_cast hh')
    constructor
    · apply (le_div_iff₀ hcA).mpr
      have hlow : A.card ≤ (L.finsetMul A (B j)).card := L.finsetMul_card_lower hc A (B j) hnon (by
        intro a ha b hb
        obtain ⟨z,hz⟩ := hA.allProducts [a,b] (by simp) (by aesop)
        exact ⟨z,(LocalGroupAlgebra.Product.pair_iff L _ _ _).1 hz⟩)
      simpa only [one_mul] using (show (A.card : ℝ) ≤ (L.finsetMul A (B j)).card by exact_mod_cast hlow)
    · apply (div_le_iff₀ hcA).mpr
      have hh := (Finset.card_le_card (L.finsetMul_mono (Finset.Subset.refl A) (hBA j))).trans
        (L.finsetMul_card_le_doubling hA (Finset.Subset.refl A))
      exact_mod_cast hh
  obtain ⟨j,hj,hplateau⟩ := exists_multiplicative_plateau f (K : ℝ) ε N hε hbound hN
  refine ⟨densityScale (K : ℝ) j,densityScale (K : ℝ) (j+1),B j,
    (densityScale_pos_le_one (K : ℝ) hKr j).1,(densityScale_pos_le_one (K : ℝ) hKr j).2,rfl,
    densityScale_antitone (K : ℝ) hKr (by omega),hBA j,hBsize j,?_⟩
  intro C hCA hC
  have hh : ((L.finsetMul A (B (j+1))).card : ℝ) ≤ (L.finsetMul A C).card := by exact_mod_cast hmin (j+1) C hCA hC
  have hp := mul_le_mul_of_nonneg_right hplateau hcA.le
  dsimp [f] at hp
  field_simp at hp
  nlinarith
end DirectedCycles
