module

public import DirectedCycles.InternalCountableSaturation
public import DirectedCycles.InternalSetLogic

@[expose] public section

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- A countable internal cover of an internal set has a finite subcover.
This is the exact combinatorial compactness statement used for the model
construction; no ambient compact topology is assumed. -/
theorem internal_countable_cover_finite (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ Filter.atTop)
    (G : ℕ → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) (B : ℕ → ∀ i, Set (G i))
    (hcover : ∀ z ∈ ultraSet (u : Filter ℕ) G A,
      ∃ n, z ∈ ultraSet (u : Filter ℕ) G (B n)) :
    ∃ N : ℕ, ∀ z ∈ ultraSet (u : Filter ℕ) G A,
      ∃ n ≤ N, z ∈ ultraSet (u : Filter ℕ) G (B n) := by
  classical
  by_contra! hnot
  let C : ℕ → ∀ i, Set (G i) := fun n i => A i ∩ (B n i)ᶜ
  have hC : ∀ n, ultraSet (u : Filter ℕ) G (C n) =
      ultraSet (u : Filter ℕ) G A ∩ (ultraSet (u : Filter ℕ) G (B n))ᶜ := by
    intro n
    exact (ultraSet_inter _ G _ _).trans (by rw [ultraSet_compl])
  have hfinite : ∀ N, ∃ z : GroupUltraproduct (u : Filter ℕ) G,
      ∀ n ≤ N, z ∈ ultraSet (u : Filter ℕ) G (C n) := by
    intro N
    obtain ⟨z,hz,hzB⟩ := hnot N
    refine ⟨z,?_⟩
    intro n hn
    rw [hC]
    exact ⟨hz,hzB n hn⟩
  obtain ⟨z,hz⟩ := internal_countable_saturation (u : Filter ℕ) hu G C hfinite
  have hzA : z ∈ ultraSet (u : Filter ℕ) G A := by
    have hh := hz 0
    rw [hC] at hh
    exact hh.1
  obtain ⟨n,hn⟩ := hcover z hzA
  have hh := hz n
  rw [hC] at hh
  exact hh.2 hn

end DirectedCycles
