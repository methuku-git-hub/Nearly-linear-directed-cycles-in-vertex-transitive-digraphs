import DirectedCycles.CyclicWordExit
import DirectedCycles.TrappingLimitSubgroup

set_option autoImplicit false
open Filter
open scoped Topology Pointwise
namespace DirectedCycles

/-- Ordinary choice of two witness families from an eventual existence statement. -/
theorem eventual_pair_choice {ι α β : Type*} [Nonempty α] [Nonempty β]
    {l : Filter ι} {P : ι → α → β → Prop}
    (h : ∀ᶠ i in l, ∃ a b, P i a b) :
    ∃ (a : ι → α) (b : ι → β), ∀ᶠ i in l, P i (a i) (b i) := by
  classical
  have hc : ∀ i, ∃ a b, (∃ a b, P i a b) → P i a b := by
    intro i
    by_cases hi : ∃ a b, P i a b
    · obtain ⟨a,b,hab⟩ := hi
      exact ⟨a,b,fun _ => hab⟩
    · exact ⟨Classical.choice inferInstance,Classical.choice inferInstance,fun hi' => (hi hi').elim⟩
  choose a b hab using hc
  exact ⟨a,b,h.mono (fun i hi => hab i hi)⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The first exits from a smaller window have no larger radius, and
actual exiting group elements can be chosen along the same filter. -/
theorem smaller_word_exit_selection {ι : Type*} {l : Filter ι}
    (Q : ι → Set G) (r : ι → ℕ) {U O : Set G} (hO : IsOpen O)
    (hO1 : (1 : G) ∈ O) (hOU : O ⊆ U)
    (hQ1 : ∀ i, (1 : G) ∈ Q i) (hQi : ∀ i, (Q i)⁻¹ = Q i)
    (hsmall : ∀ V : Set G, IsOpen V → (1 : G) ∈ V →
      ∀ᶠ i in l, ∀ q ∈ Q i, ∀ j : ℕ, q^j ∈ V)
    (hfail : ∀ᶠ i in l, ¬ (Subgroup.closure (Q i) : Set G) ⊆ U)
    (hrmax : ∀ᶠ i in l, ∀ k : ℕ, (Q i)^k ⊆ U → k ≤ r i) :
    ∃ (s : ι → ℕ) (g : ι → G), ∀ᶠ i in l,
      0 < s i ∧ s i ≤ r i ∧ (Q i)^(s i) ⊆ O ∧
        g i ∈ (Q i)^(s i+1) ∧ g i ∉ O := by
  apply eventual_pair_choice (P := fun i s g =>
    0 < s ∧ s ≤ r i ∧ (Q i)^s ⊆ O ∧ g ∈ (Q i)^(s+1) ∧ g ∉ O)
  filter_upwards [hsmall O hO hO1,hfail,hrmax] with i hi hfi hri
  have hQO : Q i ⊆ O := fun x hx => by simpa only [pow_one] using hi x hx 1
  obtain ⟨e⟩ := word_exit_radius_exists (hQ1 i) (hQi i) hQO
    (fun h => hfi (h.trans hOU))
  obtain ⟨g,hg,hgo⟩ := Set.not_subset.mp e.exits
  exact ⟨e.radius,g,e.positive,hri e.radius (e.inside.trans hOU),e.inside,hg,hgo⟩
end DirectedCycles
