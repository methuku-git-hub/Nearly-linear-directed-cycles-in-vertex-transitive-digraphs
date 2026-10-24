import DirectedCycles.LocalCentralProperProgression
import DirectedCycles.LocalAmbientCentralCommutators

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} [Fintype G] {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- The finite central induction step assembles actual word domains,
proper ordered coordinates, the density bound, and ambient commutator
vanishing. The only length threshold is explicit and is eventually met
by unbounded input lengths. No normal-form conclusion is asserted. -/
theorem central_progression_step_of_budget (hd : L.DivisionClosed) (hr : L.Reversible)
    (B : Finset G) {K : ℕ} (hB : IsStrongLocalFiniteApproximateGroup L K B)
    (hBD : (B : Set G) ⊆ D.small)
    {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hcontrol : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm B x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B) y)
    (hcentral : ∀ p ∈ P, ∀ b ∈ B, L.Commute p b)
    (r T : ℕ) (hT : 3 ≤ T)
    (hlarge : (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)) * (max C C₀) * ((r+1 : ℕ) : ℝ) < T) : ∀ (g : Fin r → D.Carrier) (N : Fin r → ℕ),
      (∀ i, 1 ≤ N i) →
      ∀ hq : D.algebra.SignedWordsIn g N (D.finiteImage B),
      Function.Injective (D.algebra.orderedGrid hq) →
      ∀ (u : D.small) (n W : ℕ), 2 ≤ n → u.val ≠ L.one →
      L.escapeNorm B u.val ≤ C₀/((n : ℝ)+1) →
      ∀ p : L.PowerSegment u.val W, n ≤ W →
      ∀ (A : Set G), L.IsNSS A → (∀ x ∈ A, ∀ y ∈ A, L.Defined x y) →
      (∀ m < n, p.power m ∈ A) →
      (∀ k : ℤ, k.natAbs < n → p.signedPower k ∈ P) →
      ∀ c : ℕ, (∀ x, D.algebra.GeneratorCommutators (Set.range g) c x → x = D.algebra.one) →
      (∀ i : Fin (r+1), 4^(c+2) ≤ (Fin.lastCases n N i)/T) →
      ∀ a J Jq : ℕ, a ≤ J*(D.finiteImage B).card*(2*n-1) →
      (D.finiteImage B).card ≤ Jq * ∏ i, (2*N i+1) →
      ∃ v : Fin (r+1) → D.small,
        v (Fin.last r) = u ∧ (∀ i, D.project (v i.castSucc) = g i) ∧
        ∃ hw : L.SignedWordsIn (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) B,
          Function.Injective (L.orderedGrid hw) ∧
          L.wordProgression (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) ⊆ B ∧
          (∀ x, L.GeneratorCommutators (Set.range (fun i => (v i).val)) (c+1) x → x = L.one) ∧
          a ≤ (J*Jq*(2*T)^(r+1)) * ∏ i : Fin (r+1), (2*((Fin.lastCases n N i)/T)+1) := by
  have hlift := D.central_proper_progression_lift_of_budget hd hr B hB hBD hC hC₀ hcontrol r T hT hlarge
  intro g N hN hq hproper u n W hn hu he p hnW A hNSS hdom hprev hkernel c hc hbudget a J Jq ha hqcard
  obtain ⟨v,hvlast,hvprefix,hw,hproperv,hsub⟩ :=
    hlift g N hN hq hproper u n W (by omega) hu he p hnW A hNSS hdom hprev hkernel
  refine ⟨v,hvlast,hvprefix,hw,hproperv,hsub,?_,?_⟩
  · have huP : u.val ∈ P := by
      have hh := hkernel 1 (by norm_num; omega)
      have hp1 : p.signedPower (1 : ℤ) = u.val :=
        (p.signedPower_nat 1).trans (p.one (by omega))
      exact hp1 ▸ hh
    have hlast : D.project (v (Fin.last r)) = D.algebra.one := by
      rw [hvlast]
      exact (D.project_eq_one_iff_mem u).2 huP
    have hqfull := D.quotient_prefix_commutators_vanish hr v g hvprefix hlast c hc
    have hwordsD := hw.mono L (fun _ => le_rfl) hBD
    apply D.ambient_generatorCommutators_central_step hr v (fun i => (Fin.lastCases n N i)/T)
      hwordsD c hbudget ?_ hqfull
    intro x hx i
    apply hcentral x hx (v i).val
    apply hw.generator_mem L i
    have hpow : 0 < 4^(c+2) := pow_pos (by decide) _
    exact hpow.trans_le (hbudget i)
  · have hh := central_box_density N (by omega : 0 < T) ha hqcard (by omega : 2*n-1 ≤ 2*n+1)
    simpa only [Fin.prod_univ_castSucc,Fin.lastCases_castSucc,Fin.lastCases_last] using hh

/-- The shrinking factor depends only on K, the rank and the two lift bounds. -/
theorem central_progression_step (hd : L.DivisionClosed) (hr : L.Reversible)
    (B : Finset G) {K : ℕ} (hB : IsStrongLocalFiniteApproximateGroup L K B)
    (hBD : (B : Set G) ⊆ D.small)
    {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hcontrol : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm B x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B) y)
    (hcentral : ∀ p ∈ P, ∀ b ∈ B, L.Commute p b)
    (r : ℕ) :
    ∃ T : ℕ, 3 ≤ T ∧ ∀ (g : Fin r → D.Carrier) (N : Fin r → ℕ),
      (∀ i, 1 ≤ N i) →
      ∀ hq : D.algebra.SignedWordsIn g N (D.finiteImage B),
      Function.Injective (D.algebra.orderedGrid hq) →
      ∀ (u : D.small) (n W : ℕ), 2 ≤ n → u.val ≠ L.one →
      L.escapeNorm B u.val ≤ C₀/((n : ℝ)+1) →
      ∀ p : L.PowerSegment u.val W, n ≤ W →
      ∀ (A : Set G), L.IsNSS A → (∀ x ∈ A, ∀ y ∈ A, L.Defined x y) →
      (∀ m < n, p.power m ∈ A) →
      (∀ k : ℤ, k.natAbs < n → p.signedPower k ∈ P) →
      ∀ c : ℕ, (∀ x, D.algebra.GeneratorCommutators (Set.range g) c x → x = D.algebra.one) →
      (∀ i : Fin (r+1), 4^(c+2) ≤ (Fin.lastCases n N i)/T) →
      ∀ a J Jq : ℕ, a ≤ J*(D.finiteImage B).card*(2*n-1) →
      (D.finiteImage B).card ≤ Jq * ∏ i, (2*N i+1) →
      ∃ v : Fin (r+1) → D.small,
        v (Fin.last r) = u ∧ (∀ i, D.project (v i.castSucc) = g i) ∧
        ∃ hw : L.SignedWordsIn (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) B,
          Function.Injective (L.orderedGrid hw) ∧
          L.wordProgression (fun i => (v i).val) (fun i => (Fin.lastCases n N i)/T) ⊆ B ∧
          (∀ x, L.GeneratorCommutators (Set.range (fun i => (v i).val)) (c+1) x → x = L.one) ∧
          a ≤ (J*Jq*(2*T)^(r+1)) * ∏ i : Fin (r+1), (2*((Fin.lastCases n N i)/T)+1) := by
  obtain ⟨T,hT,hlarge⟩ := central_progression_scale_exists K r C C₀
  exact ⟨T,hT,D.central_progression_step_of_budget hd hr B hB hBD hC hC₀ hcontrol hcentral r T hT hlarge⟩

end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
