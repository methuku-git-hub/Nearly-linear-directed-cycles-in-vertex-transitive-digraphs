module

public import DirectedCycles.LocalCentralOrderedGrid
public import DirectedCycles.LocalOrderedGridRestriction
public import DirectedCycles.LocalCentralProgressionWords
public import DirectedCycles.ProgressionShrinkingArithmetic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} [Fintype G] {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- A proper quotient progression lifts to a proper progression of one
higher rank, with every source word defined and contained in the strong
source. Uniform controlled lifts determine the sole shrinking factor. -/
theorem central_proper_progression_lift_of_budget (hd : L.DivisionClosed) (hr : L.Reversible)
    (B : Finset G) {K : ℕ} (hB : IsStrongLocalFiniteApproximateGroup L K B)
    (hBD : (B : Set G) ⊆ D.small)
    {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hcontrol : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm B x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B) y)
    (r T : ℕ) (hT : 3 ≤ T)
    (hlarge : (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)) * (max C C₀) * ((r+1 : ℕ) : ℝ) < T) : ∀ (g : Fin r → D.Carrier) (N : Fin r → ℕ),
      (∀ i, 1 ≤ N i) →
      ∀ hq : D.algebra.SignedWordsIn g N (D.finiteImage B),
      Function.Injective (D.algebra.orderedGrid hq) →
      ∀ (u : D.small) (n W : ℕ), 0 < n → u.val ≠ L.one →
      L.escapeNorm B u.val ≤ C₀/((n : ℝ)+1) →
      ∀ p : L.PowerSegment u.val W, n ≤ W →
      ∀ (A : Set G), L.IsNSS A → (∀ x ∈ A, ∀ y ∈ A, L.Defined x y) →
      (∀ m < n, p.power m ∈ A) →
      (∀ k : ℤ, k.natAbs < n → p.signedPower k ∈ P) →
      ∃ v : Fin (r+1) → D.small,
        v (Fin.last r) = u ∧ (∀ i, D.project (v i.castSucc) = g i) ∧
        ∃ hw : L.SignedWordsIn (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) B,
          Function.Injective (L.orderedGrid hw) ∧
          L.wordProgression (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) ⊆ B := by
  have hwords := D.controlled_central_progression_words_of_budget hd hr B hB hC hC₀ hcontrol r T hT hlarge
  intro g N hN hq hproper u n W hn hu he p hnW A hNSS hdom hprev hkernel
  obtain ⟨v,hvlast,hvproj,hw,hsub⟩ := hwords g N
    (fun i => hq.generator_mem D.algebra i (hN i))
    (fun i m hm => hq.generator_powers D.algebra i m hm) u n he
  subst u
  refine ⟨v,rfl,hvproj,hw,?_,hsub⟩
  let M : Fin (r+1) → ℕ := fun i => (Fin.lastCases n N i)/T
  have hwhole : L.SignedWordsIn (fun i => (v i).val) M D.small :=
    hw.mono L (fun _ => le_rfl) hBD
  have hvf : (fun i : Fin r => D.project (v i.castSucc)) = g := funext hvproj
  have hqv : D.algebra.SignedWordsIn (fun i : Fin r => D.project (v i.castSucc)) N (D.finiteImage B) := by
    simpa only [hvf] using hq
  have hproperv : Function.Injective (D.algebra.orderedGrid hqv) := by
    cases hvf
    exact hproper
  have hMN : ∀ i : Fin r, M i.castSucc ≤ N i := by
    intro i
    simp only [M,Fin.lastCases_castSucc]
    exact Nat.div_le_self _ _
  have hsmallq : D.algebra.SignedWordsIn (fun i : Fin r => D.project (v i.castSucc))
      (fun i => M i.castSucc) Set.univ := hqv.mono D.algebra hMN (Set.subset_univ _)
  have hpropersmall : Function.Injective (D.algebra.orderedGrid hsmallq) :=
    D.algebra.orderedGrid_injective_of_le hsmallq hqv hMN hproperv
  have hshort : 2*M (Fin.last r) < n := by
    simpa only [M,Fin.lastCases_last] using twice_shrunk_length_lt hn hT
  have hproperD := D.central_orderedGrid_injective hd hr hNSS hdom v M hwhole hsmallq hpropersmall
    hu p hnW hprev hshort (fun k hk => hkernel k (by omega))
  exact L.orderedGrid_injective_of_le hw hwhole (fun _ => le_rfl) hproperD

/-- The shrinking factor depends only on K, the rank and the two lift bounds. -/
theorem central_proper_progression_lift (hd : L.DivisionClosed) (hr : L.Reversible)
    (B : Finset G) {K : ℕ} (hB : IsStrongLocalFiniteApproximateGroup L K B)
    (hBD : (B : Set G) ⊆ D.small)
    {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hcontrol : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm B x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B) y)
    (r : ℕ) :
    ∃ T : ℕ, 3 ≤ T ∧ ∀ (g : Fin r → D.Carrier) (N : Fin r → ℕ),
      (∀ i, 1 ≤ N i) →
      ∀ hq : D.algebra.SignedWordsIn g N (D.finiteImage B),
      Function.Injective (D.algebra.orderedGrid hq) →
      ∀ (u : D.small) (n W : ℕ), 0 < n → u.val ≠ L.one →
      L.escapeNorm B u.val ≤ C₀/((n : ℝ)+1) →
      ∀ p : L.PowerSegment u.val W, n ≤ W →
      ∀ (A : Set G), L.IsNSS A → (∀ x ∈ A, ∀ y ∈ A, L.Defined x y) →
      (∀ m < n, p.power m ∈ A) →
      (∀ k : ℤ, k.natAbs < n → p.signedPower k ∈ P) →
      ∃ v : Fin (r+1) → D.small,
        v (Fin.last r) = u ∧ (∀ i, D.project (v i.castSucc) = g i) ∧
        ∃ hw : L.SignedWordsIn (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) B,
          Function.Injective (L.orderedGrid hw) ∧
          L.wordProgression (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) ⊆ B := by
  obtain ⟨T,hT,hlarge⟩ := central_progression_scale_exists K r C C₀
  exact ⟨T,hT,D.central_proper_progression_lift_of_budget hd hr B hB hBD hC hC₀ hcontrol r T hT hlarge⟩

end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
