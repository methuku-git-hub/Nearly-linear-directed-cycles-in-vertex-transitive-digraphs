module

public import DirectedCycles.FiniteSmallNormalNeighbourhoods

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods

/-- Uniform constants and a choice of the next finite normal neighbourhood. -/
structure NormalStepBounds (K L d : ℝ) where
  nextL : ℝ
  nextD : ℝ
  one_le : 1 ≤ nextL
  pos : 0 < nextD
  step : ∀ (G : Type*) [Group G] [DecidableEq G] (A R : Finset G),
    IsApproximateSubgroup K (A : Set G) → IsApproximateSubgroup L (R : Set G) →
    R ⊆ A^4 → d*A.card ≤ R.card →
    ∃ T : Finset G, IsApproximateSubgroup nextL (T : Set G) ∧ nextD*A.card ≤ T.card ∧
      ∀ x ∈ (A : Set G)^4, ∀ g ∈ (T : Set G)^8, x⁻¹*g*x ∈ (R : Set G)^4

noncomputable def normalStepBounds (K L d : ℝ) (hK : 1 ≤ K) (hL : 1 ≤ L) (hd : 0 < d) :
    NormalStepBounds K L d := by
  choose L' d' hL' hd' h using finite_small_normal_neighbourhoods K L d 8 hK hL hd
  exact ⟨L',d',hL',hd',h⟩

/-- A chain of finite normal neighbourhoods with constants uniform in the
ambient group. The fourth powers are the shrinking neighbourhoods. -/
theorem uniform_neighbourhood_chain (K : ℝ) (hK : 1 ≤ K) :
    ∃ L d : ℕ → ℝ, (∀ n, 1 ≤ L n ∧ 0 < d n) ∧
      ∀ (G : Type*) [Group G] [DecidableEq G] (A : Finset G),
      IsApproximateSubgroup K (A : Set G) →
      ∃ R : ℕ → Finset G, ∀ n,
        IsApproximateSubgroup (L n) (R n : Set G) ∧
        d n*A.card ≤ (R n).card ∧ (R n : Set G)^4 ⊆ (A : Set G)^4 ∧
        ∀ x ∈ (A : Set G)^4, ∀ g ∈ (R (n+1) : Set G)^8,
          x⁻¹*g*x ∈ (R n : Set G)^4 := by
  classical
  obtain ⟨L₀,d₀,hL₀,hd₀,hinit⟩ := finite_small_neighbourhoods K hK 4
  let Bounds := {p : ℝ × ℝ // 1 ≤ p.1 ∧ 0 < p.2}
  let next : Bounds → Bounds := fun p =>
    let s := normalStepBounds K p.val.1 p.val.2 hK p.property.1 p.property.2
    ⟨(s.nextL,s.nextD),s.one_le,s.pos⟩
  let b : ℕ → Bounds := fun n => next^[n] ⟨(L₀,d₀),hL₀,hd₀⟩
  have bsucc : ∀ n, b (n+1) = next (b n) := fun n => Function.iterate_succ_apply' _ _ _
  refine ⟨fun n => (b n).val.1,fun n => (b n).val.2,fun n => (b n).property,?_⟩
  intro G _ _ A hA
  let State := fun n => {S : Finset G //
    IsApproximateSubgroup (b n).val.1 (S : Set G) ∧
    (b n).val.2*A.card ≤ S.card ∧ (S : Set G)^4 ⊆ (A : Set G)^4}
  obtain ⟨R₀,hR₀,hR₀d,hR₀p⟩ := hinit G A hA
  have hinitial : State 0 := ⟨R₀,hR₀,hR₀d,hR₀p⟩
  have hnext : ∀ n (s : State n), ∃ t : State (n+1),
      ∀ x ∈ (A : Set G)^4, ∀ g ∈ (t.val : Set G)^8,
        x⁻¹*g*x ∈ (s.val : Set G)^4 := by
    intro n s
    let step := normalStepBounds K (b n).val.1 (b n).val.2 hK (b n).property.1 (b n).property.2
    have hsA : s.val ⊆ A^4 := by
      have hh := (Set.subset_pow s.property.1.one_mem (by omega : 4 ≠ 0)).trans s.property.2.2
      exact_mod_cast hh
    obtain ⟨T,hT,hTd,hTp⟩ := step.step G A s.val hA s.property.1 hsA s.property.2.1
    have hT4 : (T : Set G)^4 ⊆ (A : Set G)^4 := by
      intro g hg
      have hgp := Set.pow_subset_pow_right hT.one_mem (by omega : 4 ≤ 8) hg
      have hh := hTp 1 (Set.one_mem_pow hA.one_mem) g hgp
      exact s.property.2.2 (by simpa using hh)
    have hTL : IsApproximateSubgroup (b (n+1)).val.1 (T : Set G) := by
      simpa only [bsucc,next,step] using hT
    have hTD : (b (n+1)).val.2*A.card ≤ T.card := by
      simpa only [bsucc,next,step] using hTd
    exact ⟨⟨T,hTL,hTD,hT4⟩,hTp⟩
  let st : ∀ n, State n := fun n => Nat.rec hinitial (fun n s => Classical.choose (hnext n s)) n
  have stsucc : ∀ n, st (n+1) = Classical.choose (hnext n (st n)) := fun _ => rfl
  refine ⟨fun n => (st n).val,?_⟩
  intro n
  refine ⟨(st n).property.1,(st n).property.2.1,(st n).property.2.2,?_⟩
  change ∀ x ∈ (A : Set G)^4, ∀ g ∈ ((st (n+1)).val : Set G)^8,
    x⁻¹*g*x ∈ ((st n).val : Set G)^4
  rw [stsucc]
  exact Classical.choose_spec (hnext n (st n))

end FiniteAlmostPeriods
end DirectedCycles
