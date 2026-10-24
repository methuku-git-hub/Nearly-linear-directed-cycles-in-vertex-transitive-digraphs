import DirectedCycles.WeakComponents

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- The full orbit of one ordered pair under the given action. -/
def ArcOrbit {G V : Type*} [Group G] [MulAction G V] (a b : V) : Digraph V :=
  fun x y => ∃ g : G, g • a = x ∧ g • b = y

theorem arcOrbit_invariant {G V : Type*} [Group G] [MulAction G V]
    (a b : V) (g : G) (x y : V) :
    ArcOrbit (G := G) a b (g • x) (g • y) ↔ ArcOrbit (G := G) a b x y := by
  constructor
  · rintro ⟨h, hx, hy⟩
    refine ⟨g⁻¹ * h, ?_, ?_⟩
    · rw [mul_smul, hx, inv_smul_smul]
    · rw [mul_smul, hy, inv_smul_smul]
  · rintro ⟨h, hx, hy⟩
    exact ⟨g * h, by rw [mul_smul, hx], by rw [mul_smul, hy]⟩

theorem arcOrbit_self {G V : Type*} [Group G] [MulAction G V] (a b : V) :
    ArcOrbit (G := G) a b a b := ⟨1, one_smul _ _, one_smul _ _⟩

theorem arcOrbit_subset {G V : Type*} [Group G] [MulAction G V]
    (D : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    {a b : V} (hab : D a b) : ∀ x y, ArcOrbit (G := G) a b x y → D x y := by
  rintro x y ⟨g, rfl, rfl⟩
  exact (hD g a b).mpr hab

/-- One arc orbit contributes at most the order of the point stabilizer to
its tail's outdegree. The action need not be faithful. -/
theorem arcOrbit_degree_le_stabilizer {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [MulAction G V] (a b : V) :
    (Finset.univ.filter (ArcOrbit (G := G) a b a)).card ≤
      Fintype.card (MulAction.stabilizer G a) := by
  let f : MulAction.stabilizer G a → V := fun g => (g.val : G) • b
  have he : Finset.univ.filter (ArcOrbit (G := G) a b a) = Finset.univ.image f := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨g, hg, hy⟩
      exact ⟨⟨g, hg⟩, hy⟩
    · rintro ⟨g, hg⟩
      exact ⟨g.val, g.property, hg⟩
  rw [he]
  exact (Finset.card_image_le).trans_eq (Finset.card_univ)

/-- If the selected invariant graph is disconnected, an original arc can be
translated to leave the component at the prescribed root. -/
theorem invariant_arc_outside_component {G V : Type*} [Group G] [Fintype V]
    [MulAction G V] (D E : Digraph V) (hD : StronglyConnected D)
    (hDi : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (hEi : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (a : V) (hn : ¬ Connected E) :
    ∃ b, D a b ∧ ¬ WeakReach E a b := by
  obtain ⟨x, hx, y, hy, hxy⟩ := stronglyConnected_arc_leaving D hD
    (weakComponent E a) (weakComponent_nonempty E a)
    (fun h => hn ((weakComponent_eq_univ_iff E a).mp h))
  obtain ⟨g, hg⟩ := ht x a
  have hx' : WeakReach E a x := (mem_weakComponent _ _ _).mp hx
  have hnxy : ¬ WeakReach E x y := fun h => hy ((mem_weakComponent _ _ _).mpr (hx'.trans h))
  refine ⟨g • y, ?_, ?_⟩
  · rw [← hg]
    exact (hDi g x y).mpr hxy
  · rw [← hg]
    exact fun h => hnxy ((weakReach_invariant E hEi g x y).mp h)

end DirectedCycles
