module

public import Mathlib.Combinatorics.Additive.ApproximateSubgroup
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G] [DecidableEq G]

theorem exists_expansion_minimizer (A : Finset G) (t : ℝ) (ht : t ≤ 1) :
    ∃ B : Finset G, B ⊆ A ∧ t*A.card ≤ B.card ∧
      ∀ C : Finset G, C ⊆ A → t*A.card ≤ C.card → (A*B).card ≤ (A*C).card := by
  classical
  let F := {B ∈ A.powerset | t*A.card ≤ (B.card : ℝ)}
  have hFA : A ∈ F := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),by nlinarith [Nat.cast_nonneg (α := ℝ) A.card]⟩
  obtain ⟨B,hB,hmin⟩ := F.exists_min_image (fun B => (A*B).card) ⟨A,hFA⟩
  obtain ⟨hBA,hBt⟩ := Finset.mem_filter.mp hB
  refine ⟨B,Finset.mem_powerset.mp hBA,hBt,?_⟩
  intro C hCA hCt
  exact hmin C (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hCA,hCt⟩)

/-- A bounded positive sequence cannot lose a fixed relative fraction at
every step. This elementary form gives a uniform finite search bound. -/
theorem exists_multiplicative_plateau (f : ℕ → ℝ) (K ε : ℝ) (N : ℕ)
    (hε : 0 < ε) (hbound : ∀ j ≤ N, 1 ≤ f j ∧ f j ≤ K)
    (hN : K ≤ N*ε) :
    ∃ j < N, (1-ε)*f j ≤ f (j+1) := by
  by_contra! hnot
  have hdec : ∀ j ≤ N, f j ≤ K-j*ε := by
    intro j hj
    induction j with
    | zero => simpa using (hbound 0 (Nat.zero_le _)).2
    | succ j ih =>
      have hjN : j < N := by omega
      have hi := ih (Nat.le_of_lt hjN)
      have hh := hnot j hjN
      have hl := (hbound j (Nat.le_of_lt hjN)).1
      have hm := mul_nonneg hε.le (sub_nonneg.mpr hl)
      push_cast
      nlinarith
  have hl := (hbound N le_rfl).1
  have hu := hdec N le_rfl
  linarith

noncomputable def densityScale (K : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => (densityScale K n)^2/(2*K)

theorem densityScale_pos_le_one (K : ℝ) (hK : 1 ≤ K) (n : ℕ) :
    0 < densityScale K n ∧ densityScale K n ≤ 1 := by
  induction n with
  | zero => norm_num [densityScale]
  | succ n ih =>
    dsimp [densityScale]
    constructor
    · exact div_pos (sq_pos_of_pos ih.1) (by linarith)
    · apply (div_le_iff₀ (by linarith : 0 < 2*K)).mpr
      nlinarith

theorem densityScale_antitone (K : ℝ) (hK : 1 ≤ K) : Antitone (densityScale K) := by
  apply antitone_nat_of_succ_le
  intro n
  have hn := densityScale_pos_le_one K hK n
  change (densityScale K n)^2/(2*K) ≤ densityScale K n
  apply (div_le_iff₀ (by linarith : 0 < 2*K)).mpr
  have := mul_le_mul_of_nonneg_left hK hn.1.le
  nlinarith

/-- Uniform scale selection for Sanders' argument, with actual minimizing
subsets of the finite approximate group. -/
theorem uniform_expansion_scale (K ε : ℝ) (hK : 1 ≤ K) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (G : Type*) [Group G] [DecidableEq G]
      (A : Finset G), IsApproximateSubgroup K (A : Set G) →
      ∃ (t δ : ℝ) (B : Finset G),
        0 < t ∧ t ≤ 1 ∧ δ = t^2/(2*K) ∧ δ₀ ≤ δ ∧
        B ⊆ A ∧ t*A.card ≤ B.card ∧
        ∀ C : Finset G, C ⊆ A → δ*A.card ≤ C.card →
          (1-ε)*(A*B).card ≤ (A*C).card := by
  classical
  let N := ⌈K/ε⌉₊
  have hN : K ≤ N*ε := (div_le_iff₀ hε).mp (Nat.le_ceil (K/ε))
  refine ⟨densityScale K N,(densityScale_pos_le_one K hK N).1,?_⟩
  intro G _ _ A hA
  have hcA : (0 : ℝ) < A.card := by
    exact_mod_cast (show A.Nonempty from ⟨1,hA.one_mem⟩).card_pos
  have hex : ∀ j : ℕ, ∃ B : Finset G, B ⊆ A ∧ densityScale K j*A.card ≤ B.card ∧
      ∀ C : Finset G, C ⊆ A → densityScale K j*A.card ≤ C.card →
        (A*B).card ≤ (A*C).card := fun j =>
      exists_expansion_minimizer A (densityScale K j) (densityScale_pos_le_one K hK j).2
  choose B hBA hBsize hmin using hex
  let f := fun j => ((A*B j).card : ℝ)/A.card
  have hbound : ∀ j ≤ N, 1 ≤ f j ∧ f j ≤ K := by
    intro j hj
    have hnon : (B j).Nonempty := Finset.card_pos.mp (by
      have hh := mul_pos (densityScale_pos_le_one K hK j).1 hcA
      have : (0 : ℝ) < (B j).card := hh.trans_le (hBsize j)
      exact_mod_cast this)
    constructor
    · apply (le_div_iff₀ hcA).mpr
      simpa only [one_mul] using (show (A.card : ℝ) ≤ (A*B j).card by
        exact_mod_cast (Finset.card_le_card_mul_right hnon : A.card ≤ (A*B j).card))
    · apply (div_le_iff₀ hcA).mpr
      have hh : (A*B j).card ≤ (A*A).card :=
        Finset.card_le_card (Finset.mul_subset_mul (Finset.Subset.refl _) (hBA j))
      exact (show ((A*B j).card : ℝ) ≤ (A*A).card from by exact_mod_cast hh).trans hA.card_mul_self_le
  obtain ⟨j,hj,hplateau⟩ := exists_multiplicative_plateau f K ε N hε hbound hN
  refine ⟨densityScale K j,densityScale K (j+1),B j,
    (densityScale_pos_le_one K hK j).1,(densityScale_pos_le_one K hK j).2,rfl,
    densityScale_antitone K hK (by omega),hBA j,hBsize j,?_⟩
  intro C hCA hC
  have hh : ((A*B (j+1)).card : ℝ) ≤ (A*C).card := by exact_mod_cast hmin (j+1) C hCA hC
  have hp := mul_le_mul_of_nonneg_right hplateau hcA.le
  dsimp [f] at hp
  field_simp at hp
  nlinarith

end FiniteAlmostPeriods
end DirectedCycles
