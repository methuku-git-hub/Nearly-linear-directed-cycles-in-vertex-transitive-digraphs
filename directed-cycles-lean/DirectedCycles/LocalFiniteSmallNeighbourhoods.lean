import DirectedCycles.LocalDenseAlmostPeriods
import DirectedCycles.LocalExpansionMinimizers
import DirectedCycles.LocalAlmostPeriodPowers
import DirectedCycles.LocalPackingCover
import DirectedCycles.LocalApproximatePowerCard

set_option autoImplicit false
namespace DirectedCycles

/-- Uniform finite small neighbourhoods for actual local approximate groups.
Both the long-product domain and the symmetric finite cover are constructed;
no embedding of the local group in a global group is used. -/
theorem local_finite_small_neighbourhoods (K : ℕ) (hK : 1 ≤ K) (m : ℕ) :
    ∃ (J : ℕ) (δ : ℝ), 1 ≤ J ∧ 0 < δ ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G), L.DivisionClosed → L.Reversible →
      ∀ A : Finset G, IsLocalFiniteApproximateGroup L K A →
      ∃ B : Finset G, IsLocalFiniteApproximateGroup L J B ∧
        δ*A.card ≤ B.card ∧ L.AllProductsDefined (B : Set G) m ∧
        (∀ n ≤ m, L.wordPower (B : Set G) n ⊆ L.wordPower (A : Set G) 4) := by
  classical
  let N := 400+2*m
  let ε : ℝ := 1/((N : ℝ)+1)
  have hden : (0 : ℝ) < (N : ℝ)+1 := by positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  have hNε : (N : ℝ)*ε < 1 := by
    dsimp only [ε]
    rw [mul_one_div]
    exact (div_lt_one hden).mpr (by linarith)
  obtain ⟨δ,hδ,hscale⟩ := local_uniform_expansion_scale K hK ε hε
  let J := max 1 ⌈(K : ℝ)^3/δ⌉₊
  refine ⟨2*J,δ,by dsimp only [J]; omega,hδ,?_⟩
  intro G _ L hd hr A hA
  have hc := hd.cancellative L hr
  obtain ⟨t,d,D,ht,_,hdscale,hδd,hDA,hD,hmin⟩ := hscale G L hc A hA
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hd0 : 0 < d := by rw [hdscale]; exact div_pos (sq_pos_of_pos ht) (by positivity)
  have hds : 2*d*(K : ℝ) ≤ t^2 := by
    rw [hdscale]
    field_simp
    nlinarith
  obtain ⟨S,hS1,hSi,hSA,hSd,hperiod⟩ := L.dense_almost_periods hd hr A D ε t d hA hε.le ht.le hd0.le hDA hD hds hmin
  have hScard : δ*A.card ≤ (S.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hδd (Nat.cast_nonneg A.card)).trans hSd
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA.one_mem⟩
  have hDnon : D.Nonempty := Finset.card_pos.mp (by
    have hp : (0 : ℝ) < D.card := (mul_pos ht hAcard).trans_le hD
    exact_mod_cast hp)
  have hADnon : (L.finsetMul A D).Nonempty := by
    obtain ⟨d,hdD⟩ := hDnon
    exact ⟨d,(L.mem_finsetMul A D d).2 ⟨L.one,hA.one_mem,d,hdD,L.one_mul d⟩⟩
  have hAD2 : (L.finsetMul A D : Set G) ⊆ L.wordPower (A : Set G) 2 := by
    intro x hx
    obtain ⟨a,ha,d,hdD,hm⟩ := (L.mem_finsetMul A D x).1 hx
    exact ⟨[a,d],rfl,by aesop,(LocalGroupAlgebra.Product.pair_iff L _ _ _).2 hm⟩
  obtain ⟨hSdom,hSpow⟩ := L.almost_period_domains hd hr hA (L.finsetMul A D)
    hADnon.card_pos hAD2 (S : Set G) ε hε.le N hNε hperiod
  have hpacking : Nat.card (L.wordPower (S : Set G) 5) ≤ J*S.card := by
    have hbound := (Nat.card_le_card_of_injective (Set.inclusion (hSpow 5 (by dsimp only [N]; omega)))
      (Set.inclusion_injective _)).trans (local_approximate_card_power hA 3 (by norm_num))
    have hJ : (K : ℝ)^3/δ ≤ J := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 ⌈(K : ℝ)^3/δ⌉₊))
    have hcoeff : (K : ℝ)^3 ≤ (J : ℝ)*δ := (div_le_iff₀ hδ).mp hJ
    have hsize : (K : ℝ)^3*A.card ≤ (J : ℝ)*S.card := by
      nlinarith [Nat.cast_nonneg (α := ℝ) J]
    have hsize' : K^3*A.card ≤ J*S.card := by exact_mod_cast hsize
    exact hbound.trans hsize'
  let B := (L.wordPower (S : Set G) 2).toFinset
  have hBcoe : (B : Set G) = L.wordPower (S : Set G) 2 := Set.coe_toFinset _
  refine ⟨B,L.square_approximate_of_packing hd hr S hS1 hSi hSdom (by dsimp only [N]; omega)
    (le_max_left 1 _) hpacking,?_,?_,?_⟩
  · have hSB : S ⊆ B := by
      intro s hs
      apply Set.mem_toFinset.mpr
      exact L.wordPower_subset_wordPower hS1 hSdom (by omega : 1 ≤ 2) (by dsimp only [N]; omega)
        (by rw [L.wordPower_one]; exact hs)
    exact hScard.trans (by exact_mod_cast Finset.card_le_card hSB)
  · rw [hBcoe]
    exact hSdom.wordPower L (by dsimp only [N]; omega)
  · intro n hn
    rw [hBcoe]
    exact (L.wordPower_wordPower_subset hSdom 2 n (by dsimp only [N]; omega)).trans
      (hSpow (2*n) (by dsimp only [N]; omega))
end DirectedCycles
