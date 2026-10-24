import DirectedCycles.ArcOrbits
import DirectedCycles.Matching

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- After `k` orbit additions, either the selected graph is connected or its
root component has at least `2^k` vertices. -/
theorem sparse_invariant_steps {G V : Type*} [Group G] [Fintype G] [Fintype V]
    [MulAction G V] (D : Digraph V) (hD : StronglyConnected D)
    (hDi : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (a : V) (B : ℕ)
    (hB : Fintype.card (MulAction.stabilizer G a) ≤ B) (k : ℕ) :
    ∃ E : Digraph V, (∀ x y, E x y → D x y) ∧
      (∀ (g : G) x y, E (g • x) (g • y) ↔ E x y) ∧
      (Finset.univ.filter (E a)).card ≤ B * k ∧
      (Connected E ∨ 2 ^ k ≤ (weakComponent E a).card) := by
  classical
  induction k with
  | zero =>
    refine ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ _ => Iff.rfl, ?_, Or.inr ?_⟩
    · simp
    · have hp := (weakComponent_nonempty (fun _ _ => False) a).card_pos
      simpa using hp
  | succ k ih =>
    obtain ⟨E, hED, hEi, hdeg, hsize⟩ := ih
    by_cases hc : Connected E
    · refine ⟨E, hED, hEi, ?_, Or.inl hc⟩
      exact hdeg.trans (Nat.mul_le_mul_left B (Nat.le_succ k))
    · obtain ⟨b, hab, hnot⟩ := invariant_arc_outside_component D E hD hDi hEi ht a hc
      let F : Digraph V := fun x y => E x y ∨ ArcOrbit (G := G) a b x y
      have hEF : ∀ x y, E x y → F x y := fun _ _ => Or.inl
      refine ⟨F, ?_, ?_, ?_, Or.inr ?_⟩
      · intro x y h
        exact h.elim (hED x y) (arcOrbit_subset D hDi hab x y)
      · intro g x y
        exact or_congr (hEi g x y) (arcOrbit_invariant a b g x y)
      · have heq : @Finset.filter V (F a) (fun v => Classical.propDecidable (F a v)) Finset.univ =
            Finset.univ.filter (E a) ∪ Finset.univ.filter (ArcOrbit (G := G) a b a) := by
          ext y
          simp [F]
        rw [heq]
        have hbound := (arcOrbit_degree_le_stabilizer (G := G) a b).trans hB
        have hu := Finset.card_union_le (Finset.univ.filter (E a))
          (Finset.univ.filter (ArcOrbit (G := G) a b a))
        nlinarith
      · have hg := weakComponent_doubles E F hEi hEF ht a b hnot
          (Or.inr (arcOrbit_self (G := G) a b))
        have hs := hsize.resolve_left hc
        rw [pow_succ]
        omega

/-- Exact logarithmic rounding used in the sparse quotient bound. -/
theorem card_le_two_pow_ceil_log_ratio (q : ℕ) (hq : 0 < q) :
    q ≤ 2 ^ ⌈(Real.log (q : ℝ) / Real.log 2)⌉₊ := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (q : ℝ) ≤ (2 : ℝ) ^ ⌈(Real.log (q : ℝ) / Real.log 2)⌉₊ := by
    apply (Real.log_le_log_iff hq' (by positivity)).mp
    rw [Real.log_pow]
    have hc := Nat.le_ceil ((Real.log (q : ℝ) / Real.log 2))
    change Real.log (q : ℝ) / Real.log 2 ≤ _ at hc
    exact (div_le_iff₀ h2).mp hc
  exact_mod_cast hp

/-- The doubling construction terminates within the advertised number of
arc orbits, retaining a bound on the outdegree at the prescribed root. -/
theorem sparse_invariant_connected {G V : Type*} [Group G] [Fintype G] [Fintype V]
    [MulAction G V] (D : Digraph V) (hD : StronglyConnected D)
    (hDi : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (a : V) (B : ℕ)
    (hB : Fintype.card (MulAction.stabilizer G a) ≤ B) :
    ∃ E : Digraph V, (∀ x y, E x y → D x y) ∧
      (∀ (g : G) x y, E (g • x) (g • y) ↔ E x y) ∧
      (Finset.univ.filter (E a)).card ≤ B * ⌈(Real.log (Fintype.card V : ℝ) / Real.log 2)⌉₊ ∧
      StronglyConnected E := by
  obtain ⟨E, hED, hEi, hdeg, hc⟩ := sparse_invariant_steps D hD hDi ht a B hB
    ⌈(Real.log (Fintype.card V : ℝ) / Real.log 2)⌉₊
  refine ⟨E, hED, hEi, hdeg, ?_⟩
  apply (vertexTransitive_connected_iff_stronglyConnected
    (vertexTransitive_of_action E hEi ht)).mp
  rcases hc with hc | hc
  · exact hc
  · apply (weakComponent_eq_univ_iff E a).mp
    apply Finset.eq_univ_of_card
    apply Nat.le_antisymm (Finset.card_le_univ _)
    exact (card_le_two_pow_ceil_log_ratio _ (Fintype.card_pos_iff.mpr ⟨a⟩)).trans hc

/-- Manuscript Lemma 4.3, including containment, invariance, strong connectivity,
common positive in/outdegree and the exact logarithmic degree bound. -/
theorem sparse_invariant_subdigraph {G V : Type*} [Group G] [Fintype G] [Fintype V]
    [MulAction G V] (D : Digraph V) (hloop : Loopless D) (hD : StronglyConnected D)
    (hDi : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (hq : 2 ≤ Fintype.card V)
    (B : ℕ) (hB : ∀ a : V, Fintype.card (MulAction.stabilizer G a) ≤ B) :
    ∃ E : Digraph V, ∃ d : ℕ, (∀ x y, E x y → D x y) ∧ Loopless E ∧
      (∀ (g : G) x y, E (g • x) (g • y) ↔ E x y) ∧ StronglyConnected E ∧
      (∀ x, (Finset.univ.filter (E x)).card = d) ∧
      (∀ y, (Finset.univ.filter (fun x => E x y)).card = d) ∧
      1 ≤ d ∧ d ≤ B * ⌈(Real.log (Fintype.card V : ℝ) / Real.log 2)⌉₊ := by
  have hpos : 0 < Fintype.card V := by omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨E, hED, hEi, hdeg, hE⟩ := sparse_invariant_connected D hD hDi ht a B (hB a)
  have hne : ∃ x y, E x y := by
    have hp : ({a} : Finset V) ≠ Finset.univ := by
      intro he
      have hcard := congrArg Finset.card he
      simp only [Finset.card_singleton, Finset.card_univ] at hcard
      omega
    obtain ⟨x, _, y, _, hxy⟩ := stronglyConnected_arc_leaving E hE {a} (by simp) hp
    exact ⟨x, y, hxy⟩
  obtain ⟨d, hd, hl, hr, _⟩ := symmetry_matching ht ht rfl E hne hEi
  refine ⟨E, d, hED, fun x hx => hloop x (hED x x hx), hEi, hE, hl, hr, hd, ?_⟩
  rw [← hl a]
  exact hdeg

end DirectedCycles
