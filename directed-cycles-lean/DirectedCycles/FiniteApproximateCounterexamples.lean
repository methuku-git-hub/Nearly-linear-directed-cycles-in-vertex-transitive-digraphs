import DirectedCycles.CosetModelBounds

set_option autoImplicit false
namespace DirectedCycles

/-- A finite approximate group with its actual ambient group structure.
This is data, not an assumption of a structural theorem. -/
structure FiniteApproximateExample (K : ℝ) where
  carrier : Type
  group : Group carrier
  finite : Finite carrier
  set : Set carrier
  approximate : letI := group; IsApproximateSubgroup K set

instance {K : ℝ} (X : FiniteApproximateExample K) : Group X.carrier := X.group
instance {K : ℝ} (X : FiniteApproximateExample K) : Finite X.carrier := X.finite

theorem finite_coset_input_iff_examples : FiniteCosetNilprogressionTheorem ↔
    ∀ K : ℝ, 1 ≤ K → ∃ n : ℕ, 1 ≤ n ∧
      ∀ X : FiniteApproximateExample K, HasCosetNilprogressionModel X.set n := by
  rw [finite_coset_input_iff_uniform_bound]
  constructor
  · intro h K hK
    obtain ⟨n,hn,hmodel⟩ := h K hK
    exact ⟨n,hn,fun X => hmodel X.carrier X.set X.approximate⟩
  · intro h K hK
    obtain ⟨n,hn,hmodel⟩ := h K hK
    refine ⟨n,hn,?_⟩
    intro G instG instFin A hA
    exact hmodel ⟨G,instG,instFin,A,hA⟩

/-- Failure of the uniform finite theorem yields an actual sequence of
finite counterexamples whose set sizes tend to infinity. The bound n+1
avoids any exceptional zero-size parameter. -/
theorem finite_coset_counterexample_sequence (hnot : ¬ FiniteCosetNilprogressionTheorem) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ X : ℕ → FiniteApproximateExample K,
      (∀ n, ¬ HasCosetNilprogressionModel (X n).set (n+1)) ∧
      (∀ n, n+1 < Nat.card (X n).set) := by
  classical
  rw [finite_coset_input_iff_examples] at hnot
  push Not at hnot
  obtain ⟨K,hK,hfail⟩ := hnot
  have hex : ∀ n : ℕ, ∃ X : FiniteApproximateExample K,
      ¬ HasCosetNilprogressionModel X.set (n+1) := fun n => hfail (n+1) (by omega)
  choose X hx using hex
  refine ⟨K,hK,X,hx,?_⟩
  intro n
  by_contra hn
  exact hx n (hasCosetModel_of_card_le (X n).set (X n).approximate.one_mem (n+1) (by omega))

end DirectedCycles
