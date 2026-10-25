module

public import DirectedCycles.GroupUltraproduct
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Finset.Max

@[expose] public section

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- A diagonal choice meets every countable internal condition eventually.
Only cofinality of the index filter and finite satisfiability are needed. -/
theorem diagonal_internal_choice (f : Filter ℕ) (hf : f ≤ Filter.atTop)
    (G : ℕ → Type*) [∀ i, Group (G i)] (A : ℕ → ∀ i, Set (G i))
    (hfinite : ∀ n, ∀ᶠ i in f, ∃ x : G i, ∀ k ≤ n, x ∈ A k i) :
    ∃ x : ∀ i, G i, ∀ k, ∀ᶠ i in f, x i ∈ A k i := by
  classical
  let F := fun i => (Finset.range (i+1)).filter (fun n => ∃ x : G i, ∀ k ≤ n, x ∈ A k i)
  have hw : ∀ i, ∀ h : (F i).Nonempty, ∃ x : G i, ∀ k ≤ (F i).max' h, x ∈ A k i := by
    intro i h
    exact (Finset.mem_filter.mp (Finset.max'_mem (F i) h)).2
  let x : ∀ i, G i := fun i => if h : (F i).Nonempty then Classical.choose (hw i h) else 1
  refine ⟨x,?_⟩
  intro k
  have hi : ∀ᶠ i in f, k ≤ i := (eventually_ge_atTop k).filter_mono hf
  filter_upwards [hfinite k,hi] with i hsat hki
  have hkF : k ∈ F i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hsat⟩
  have hne : (F i).Nonempty := ⟨k,hkF⟩
  have hkle : k ≤ (F i).max' hne := Finset.le_max' (F i) k hkF
  dsimp only [x]
  rw [dite_eq_left hne]
  exact Classical.choose_spec (hw i hne) k hkle

/-- The actual countable intersection property of internal sets, obtained
from finite intersections inside the quotient, not an assumed saturation axiom. -/
theorem internal_countable_saturation (f : Filter ℕ) (hf : f ≤ Filter.atTop)
    (G : ℕ → Type*) [∀ i, Group (G i)] (A : ℕ → ∀ i, Set (G i))
    (hfinite : ∀ n, ∃ z : GroupUltraproduct f G,
      ∀ k ≤ n, z ∈ ultraSet f G (A k)) :
    ∃ z : GroupUltraproduct f G, ∀ k, z ∈ ultraSet f G (A k) := by
  have hs : ∀ n, ∀ᶠ i in f, ∃ x : G i, ∀ k ≤ n, x ∈ A k i := by
    intro n
    obtain ⟨z,hz⟩ := hfinite n
    obtain ⟨x,rfl⟩ := ultraMk_surjective f G z
    have hmem : ∀ k : Fin (n+1), ∀ᶠ i in f, x i ∈ A k.val i := by
      intro k
      exact (ultraMk_mem_ultraSet_iff f G (A k.val) x).mp (hz k.val (by omega))
    have hall : ∀ᶠ i in f, ∀ k : Fin (n+1), x i ∈ A k.val i := by
      exact Filter.eventually_all.mpr hmem
    filter_upwards [hall] with i hi
    exact ⟨x i,fun k hk => hi ⟨k,by omega⟩⟩
  obtain ⟨x,hx⟩ := diagonal_internal_choice f hf G A hs
  exact ⟨ultraMk f G x,fun k => (ultraMk_mem_ultraSet_iff f G (A k) x).mpr (hx k)⟩

end DirectedCycles
