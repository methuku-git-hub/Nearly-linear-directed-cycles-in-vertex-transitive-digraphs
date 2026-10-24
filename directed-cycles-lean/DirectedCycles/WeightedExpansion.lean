import DirectedCycles.PartitionCounting
import DirectedCycles.NormalOrbits

set_option autoImplicit false
namespace DirectedCycles

/-- An equivariant symmetric relation with short underlying-undirected routes
has a directed boundary lower bound. This is the routing form of Lemma 4.1. -/
theorem weighted_expansion_relation {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V]
    (D E : Digraph V) [DecidableRel E]
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (hE : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (hrefl : ∀ x, E x x) (hsymm : ∀ {x y}, E x y → E y x)
    (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hsize : ∀ x, (Finset.univ.filter (E x)).card = m)
    (hdiam : ∀ x y, E x y → ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y,
      (P.length : ℝ) ≤ ρ) (S : Finset V) :
    crossWeight E S / (((m : ℝ) - 1) * ρ) ≤ (outBoundary D S).card ∧
    crossWeight E S / (((m : ℝ) - 1) * ρ) ≤ (inBoundary D S).card := by
  classical
  choose paths hpaths using fun p : RoutedPair E => hdiam p.val.1 p.val.2 p.property.1
  let P := fun p : RoutedPair E => (paths p).vertices
  let w := orientWeight D (familyLoad P)
  have hsupport : ∀ x y, ¬(D x y ∨ D y x) → familyLoad P x y = 0 :=
    familyLoad_support P (fun p => (paths p).chain)
  have htotal : (∑ x : V, ∑ y : V, w x y) ≤
      (Fintype.card V : ℝ) * (((m : ℝ) - 1) * ρ) := by
    rw [show (∑ x : V, ∑ y : V, w x y) = ∑ p : RoutedPair E, ((paths p).length : ℝ) by
      dsimp only [w]
      rw [orientWeight_total D _ hsupport, familyLoad_total]; rfl]
    calc (∑ p : RoutedPair E, ((paths p).length : ℝ)) ≤ ∑ _p : RoutedPair E, ρ :=
           Finset.sum_le_sum (fun p _ => hpaths p)
         _ = (Fintype.card (RoutedPair E) : ℝ) * ρ := by simp
         _ = _ := by
           rw [card_routedPair E hrefl m hsize, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)]
           push_cast
           ring
  have hbase : ∀ T : Finset V, 2 * crossWeight E T ≤ cutOut w T + cutIn w T := by
    intro T
    dsimp only [w]
    rw [orientWeight_cut D _ T hsupport]
    exact familyLoad_routed_cut E hsymm P (fun p => (paths p).head)
      (fun p => (paths p).last) T
  have hcut : 2 * crossWeight E S ≤
      cutOut (averageWeight G w) S + cutIn (averageWeight G w) S := by
    apply averageWeight_cut_lower
    intro g
    have he := crossWeight_invariant E (MulAction.toPerm g) (hE g) S
    rw [← he]
    exact hbase _
  have hnonneg : ∀ x y, 0 ≤ averageWeight G w x y :=
    averageWeight_nonneg G w (orientWeight_nonneg D _ (familyLoad_nonneg P))
  have hsup : ∀ x y, ¬D x y → averageWeight G w x y = 0 :=
    averageWeight_support G D w hD (orientWeight_support D _)
  have hcap := averageWeight_capacity G w (((m : ℝ) - 1) * ρ) ht htotal
  apply boundary_lower_bound_of_weights D (averageWeight G w) S
    (((m : ℝ) - 1) * ρ) (crossWeight E S) _ hnonneg hsup
    (averageWeight_balanced G w ht) (fun x => (hcap x).1) (fun x => (hcap x).2) hcut
  have hm' : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  exact mul_pos (sub_pos.mpr hm') (by linarith)

/-- The same estimate in the manuscript's sum-over-parts notation. -/
theorem weighted_expansion_partition {G V W : Type*} [Group G] [Fintype G]
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [MulAction G V]
    (D : Digraph V) (π : V → W)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (hπ : ∀ (g : G) x y, π (g • x) = π (g • y) ↔ π x = π y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hsize : ∀ a, (Finset.univ.filter (fun x => π x = a)).card = m)
    (hdiam : ∀ x y, π x = π y → ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y,
      (P.length : ℝ) ≤ ρ) (S : Finset V) :
    let numerator := ∑ a : W, ((S.filter (fun x => π x = a)).card : ℝ) *
      (m - ((S.filter (fun x => π x = a)).card : ℝ))
    numerator / (((m : ℝ) - 1) * ρ) ≤ (outBoundary D S).card ∧
    numerator / (((m : ℝ) - 1) * ρ) ≤ (inBoundary D S).card := by
  have he : ∀ x, (Finset.univ.filter (fun y => π x = π y)).card = m := by
    intro x
    simpa only [eq_comm] using hsize (π x)
  have h := weighted_expansion_relation D (fun x y => π x = π y) hD hπ ht
    (fun _ => rfl) (fun h => h.symm) m hm ρ hρ he hdiam S
  rw [crossWeight_equal_fibres π S m hsize] at h
  exact h

/-- Manuscript Lemma 4.1 for the orbits of an actual normal subgroup.
Ambient undirected diameter is expressed by the existence of short simple
paths in the underlying undirected relation; the paths may leave the orbit. -/
theorem directed_weighted_cut {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V]
    (H : Subgroup G) [H.Normal]
    [Fintype (Quotient (MulAction.orbitRel H V))]
    [DecidableEq (Quotient (MulAction.orbitRel H V))]
    (D : Digraph V)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hsize : ∀ a : Quotient (MulAction.orbitRel H V),
      (Finset.univ.filter (fun x => Quotient.mk'' x = a)).card = m)
    (hdiam : ∀ x y, MulAction.orbitRel H V x y →
      ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y, (P.length : ℝ) ≤ ρ)
    (S : Finset V) :
    let numerator := ∑ a : Quotient (MulAction.orbitRel H V),
      ((S.filter (fun x => Quotient.mk'' x = a)).card : ℝ) *
      (m - ((S.filter (fun x => Quotient.mk'' x = a)).card : ℝ))
    numerator / (((m : ℝ) - 1) * ρ) ≤ (outBoundary D S).card ∧
    numerator / (((m : ℝ) - 1) * ρ) ≤ (inBoundary D S).card := by
  apply weighted_expansion_partition D
    (fun x => (Quotient.mk'' x : Quotient (MulAction.orbitRel H V))) hD
    (normal_orbit_projection_invariant H) ht m hm ρ hρ hsize
  intro x y hxy
  exact hdiam x y (Quotient.exact hxy)

end DirectedCycles
