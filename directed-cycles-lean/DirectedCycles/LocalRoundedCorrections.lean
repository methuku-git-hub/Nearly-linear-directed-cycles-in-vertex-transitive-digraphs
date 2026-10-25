module

public import DirectedCycles.CentralLiftBoundedRounding
public import DirectedCycles.LocalCorrectedPowerSegment

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Choose signed corrections componentwise. Bad ratio indices are assigned
zero; every correction has the domain bound, and the quantitative error bound
holds at all good indices. -/
theorem exists_rounded_correction_family {ι : Type*} (N₀ N₁ : ι → ℕ)
    (hN₀ : ∀ i, 0 < N₀ i) (hN₁ : ∀ i, 0 < N₁ i)
    {δ t t' : ℝ} (hδ : 0 < δ) (ht : |t| ≤ (11/10)*δ)
    (ht'lo : (9/10)*δ ≤ t') (ht'hi : t' ≤ (11/10)*δ) :
    ∃ m : ι → ℤ, (∀ i, (m i).natAbs*N₁ i ≤ 2*N₀ i) ∧
      ∀ i, (N₁ i : ℝ) ≤ (11/10)*(N₀ i : ℝ) →
        ∀ n ≤ N₁ i, |(t/(N₁ i : ℝ)-(m i : ℝ)*t'/(N₀ i : ℝ))*(n : ℝ)| ≤ (121/200)*δ := by
  classical
  have hex : ∀ i, ∃ m : ℤ, m.natAbs*N₁ i ≤ 2*N₀ i ∧
      ((N₁ i : ℝ) ≤ (11/10)*(N₀ i : ℝ) →
        ∀ n ≤ N₁ i, |(t/(N₁ i : ℝ)-(m : ℝ)*t'/(N₀ i : ℝ))*(n : ℝ)| ≤ (121/200)*δ) := by
    intro i
    by_cases hi : (N₁ i : ℝ) ≤ (11/10)*(N₀ i : ℝ)
    · obtain ⟨m,hm,he⟩ := central_lift_bounded_rounding hδ ht ht'lo ht'hi
        (by exact_mod_cast hN₀ i) (by exact_mod_cast hN₁ i) hi
      refine ⟨m,?_,fun _ n hn => he n (by positivity) (by exact_mod_cast hn)⟩
      have hm' : (m.natAbs : ℝ)*(N₁ i : ℝ) ≤ 2*(N₀ i : ℝ) := by
        simpa only [Nat.cast_natAbs,Int.cast_abs] using hm
      exact_mod_cast hm'
    · exact ⟨0,by simp,fun h => (hi h).elim⟩
  choose m hm he using hex
  exact ⟨m,hm,he⟩

variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Construct the actual corrected power segment and its left-oriented
correction identity, the orientation used by the quotient equivalence. -/
theorem exists_corrected_segment_left (hd : L.DivisionClosed) (hr : L.Reversible)
    {C : Set G} (hi : ∀ x ∈ C, L.inv x ∈ C) (hdom : L.AllProductsDefined C 4)
    {g u : G} (hu : u ∈ C) {M N : ℕ} (hM : 1 ≤ M)
    (p : L.PowerSegment g M) (q : L.PowerSegment u N)
    (hp : ∀ n ≤ M, p.power n ∈ C) (hq : ∀ n ≤ N, q.power n ∈ C)
    (hgu : L.Commute g u) (k : ℤ) (hk : k.natAbs*M ≤ N) :
    ∃ h : G, L.mulRel (q.signedPower (-k)) g h ∧ ∃ s : L.PowerSegment h M,
      ∀ n ≤ M, L.mulRel (p.power n) (q.signedPower (-k*(n : ℤ))) (s.power n) := by
  obtain ⟨h,hprod,s,hs,_⟩ := p.corrected_segment L hd hr hi hdom hu hM q hp hq hgu k hk
  have hkN : (-k).natAbs ≤ N := by rw [Int.natAbs_neg]; nlinarith
  have hgc : g ∈ C := (p.one hM) ▸ hp 1 hM
  obtain ⟨z,hgz,hzg⟩ := q.commute_signedPower L hd hi
    (hdom.mono L (Set.Subset.refl _) (by omega : 3 ≤ 4)) hu hgc hgu (-k) hkN
    (fun n hn => hq n (hn.trans hkN))
  exact ⟨h,(L.unique hgz hprod) ▸ hzg,s,hs⟩
end DirectedCycles
