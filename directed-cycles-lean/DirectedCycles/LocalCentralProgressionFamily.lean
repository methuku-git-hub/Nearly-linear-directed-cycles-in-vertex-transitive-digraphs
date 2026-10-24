import DirectedCycles.LocalCentralProgressionStep
import DirectedCycles.LocalProgressionWitness
import DirectedCycles.ProgressionLengthNondegeneracy

set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators
namespace DirectedCycles

/-- The entire central progression induction step is uniform over finite
components. The quotient progression invariant gives a source invariant of
rank and step one higher, with one fixed density factor and unbounded
coordinate lengths. All finite hypotheses are used on their actual common
filter-large set. -/
theorem local_central_progression_family {ι : Type*} (F : Filter ι)
    (G : ι → Type*) [∀ i, Fintype (G i)] (L : ∀ i, LocalGroupAlgebra (G i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A B : ∀ i, Finset (G i)) (P : ∀ i, Set (G i))
    (D : ∀ i, (L i).CentralQuotientData (P i)) {K J Jq r c : ℕ}
    (hJ : 1 ≤ J) (hJq : 1 ≤ Jq) {C C₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hB : ∀ᶠ i in F, IsStrongLocalFiniteApproximateGroup (L i) K (B i))
    (hBA : ∀ i, (B i : Set (G i)) ⊆ A i) (hBD : ∀ i, (B i : Set (G i)) ⊆ (D i).small)
    (hcontrol : ∀ᶠ i in F, ∀ y ∈ (D i).finiteImage (B i), ∃ x : (D i).small,
      x.val ∈ B i ∧ (D i).project x = y ∧ (L i).escapeNorm (B i) x.val ≤
        C*(D i).algebra.escapeNorm ((D i).finiteImage (B i)) y)
    (hcentral : ∀ i, ∀ p ∈ P i, ∀ b ∈ B i, (L i).Commute p b)
    (u : ∀ i, G i) (n : ι → ℕ) (p : ∀ i, (L i).PowerSegment (u i) (2*n i))
    (hn2 : ∀ i, 2 ≤ n i) (hu : ∀ i, u i ≠ (L i).one)
    (hescape : ∀ᶠ i in F, (L i).escapeNorm (B i) (u i) ≤ C₀/((n i : ℝ)+1))
    (hNSS : ∀ i, (L i).IsNSS (A i : Set (G i)))
    (hdom : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, (L i).Defined x y)
    (hprev : ∀ i, ∀ m < n i, (p i).power m ∈ A i)
    (hkernel : ∀ i, ∀ k : ℤ, k.natAbs < n i → (p i).signedPower k ∈ P i)
    (hcard : ∀ᶠ i in F, (A i).card ≤ J*((D i).finiteImage (B i)).card*(2*n i-1))
    (g : ∀ i, Fin r → (D i).Carrier) (N : ι → Fin r → ℕ)
    (hN : ∀ j, Filter.Tendsto (fun i => N i j) F Filter.atTop)
    (hn : Filter.Tendsto n F Filter.atTop)
    (hquot : ∀ᶠ i in F, ∃ hq : (D i).algebra.SignedWordsIn (g i) (N i) ((D i).finiteImage (B i)),
      Function.Injective ((D i).algebra.orderedGrid hq) ∧
      (∀ x, (D i).algebra.GeneratorCommutators (Set.range (g i)) c x → x = (D i).algebra.one) ∧
      ((D i).finiteImage (B i)).card ≤ Jq * ∏ j, (2*N i j+1)) :
    ∃ T M : ℕ, 3 ≤ T ∧ 1 ≤ M ∧
      (∀ j : Fin (r+1), Filter.Tendsto (fun i => (Fin.lastCases (n i) (N i) j)/T) F Filter.atTop) ∧
      ∀ᶠ i in F, ∃ W : (L i).ProgressionWitness (A i : Set (G i)) (r+1) (c+1),
        W.lengths = (fun j => (Fin.lastCases (n i) (N i) j)/T) ∧
        (A i).card ≤ M * ∏ j, (2*W.lengths j+1) := by
  obtain ⟨T,hT,hlarge⟩ := central_progression_scale_exists K r C C₀
  have hT0 : 0 < T := by omega
  let M := J*Jq*(2*T)^(r+1)
  have hM : 1 ≤ M := by
    have hpow : 0 < (2*T)^(r+1) := pow_pos (by omega) _
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hpow
  refine ⟨T,M,hT,hM,central_progression_lengths_tendsto N n hN hn hT0,?_⟩
  have hbudget := central_progression_budget_eventually N n hN hn hT0 c
  have hNpos : ∀ᶠ i in F, ∀ j, 1 ≤ N i j :=
    Filter.eventually_all.2 (fun j => (hN j).eventually (Filter.eventually_ge_atTop 1))
  obtain ⟨R,hR⟩ := exists_nat_gt C₀
  have hnlarge : ∀ᶠ i in F, R ≤ n i := hn.eventually (Filter.eventually_ge_atTop R)
  filter_upwards [hB,hcontrol,hescape,hcard,hquot,hbudget,hNpos,hnlarge] with
    i hBi hci hei hcardi hqi hbudgeti hNpi hni
  have hsmall : (L i).escapeNorm (B i) (u i) < 1 := by
    apply hei.trans_lt
    apply (div_lt_one (by positivity : (0 : ℝ) < (n i : ℝ)+1)).2
    have hnr : (R : ℝ) ≤ n i := by exact_mod_cast hni
    linarith
  let uS : (D i).small :=
    ⟨u i,hBD i ((L i).mem_of_escapeNorm_lt_one hBi.approximate.one_mem hsmall)⟩
  obtain ⟨hqi,hproper,hcomm,hqcard⟩ := hqi
  obtain ⟨v,_,_,hw,hproperv,_,hcommv,hdensity⟩ :=
    (D i).central_progression_step_of_budget (hd i) (hr i) (B i) hBi (hBD i) hC hC₀ hci
      (hcentral i) r T hT hlarge (g i) (N i) hNpi hqi hproper uS (n i) (2*n i)
      (hn2 i) (hu i) hei (p i) (by omega) (A i : Set (G i)) (hNSS i) (hdom i)
      (hprev i) (hkernel i) c hcomm hbudgeti (A i).card J Jq hcardi hqcard
  have hlengths : ∀ j : Fin (r+1), 1 ≤ (Fin.lastCases (n i) (N i) j)/T := by
    intro j
    have hpow : 0 < 4^(c+2) := pow_pos (by decide) _
    exact hpow.trans_le (hbudgeti j)
  have hwa : (L i).SignedWordsIn (fun j => (v j).val)
      (fun j => (Fin.lastCases (n i) (N i) j)/T) (A i : Set (G i)) := by
    intro w hb
    obtain ⟨x,hx,hp⟩ := hw w hb
    exact ⟨x,hBA i hx,hp⟩
  have hpropera : Function.Injective ((L i).orderedGrid hwa) := (L i).orderedGrid_injective_change_set hwa hw hproperv
  let W : (L i).ProgressionWitness (A i : Set (G i)) (r+1) (c+1) := by
    refine { generators := fun j => (v j).val
             lengths := fun j => (Fin.lastCases (n i) (N i) j)/T
             lengths_pos := ?_
             words := ?_
             proper := ?_
             commutators := ?_ }
    ·
      exact hlengths
    ·
      exact hwa
    ·
      exact hpropera
    ·
      exact hcommv
  refine ⟨W,rfl,?_⟩
  exact hdensity

end DirectedCycles
