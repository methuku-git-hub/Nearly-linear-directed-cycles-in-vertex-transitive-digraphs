import DirectedCycles.MajorityConnections
import DirectedCycles.NormalPartitions
import DirectedCycles.CycleLift
import DirectedCycles.ReachabilityGrowth

set_option autoImplicit false
namespace DirectedCycles
open scoped Classical

/-- Some start in part `a` reaches a strict majority of part `b` within `u` arcs. -/
def HeavyReach {V W : Type*} [Fintype V] [DecidableEq W]
    (D : Digraph V) (π : V → W) (u m : ℕ) (a b : W) : Prop :=
  ∃ x : {v // π v = a}, m < 2 *
    (Finset.univ.filter (fun y : {v // π v = b} => ReachWithin D u x.val y.val)).card

/-- The row and column majorities needed to connect arbitrary endpoints. -/
theorem heavyReach_majorities {H V W : Type*} [Group H] [Fintype V]
    [DecidableEq W] [MulAction H V] (D : Digraph V) (π : V → W)
    (hπ : ∀ (g : H) x, π (g • x) = π x)
    (hD : ∀ (g : H) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y, π x = π y → ∃ g : H, g • x = y)
    (u m : ℕ) (hsize : ∀ a, Fintype.card {x // π x = a} = m) {a b : W}
    (h : HeavyReach D π u m a b) :
    (∀ x : {v // π v = a}, m < 2 *
      (Finset.univ.filter (fun y : {v // π v = b} => ReachWithin D u x.val y.val)).card) ∧
    (∀ y : {v // π v = b}, m < 2 *
      (Finset.univ.filter (fun x : {v // π v = a} => ReachWithin D u x.val y.val)).card) := by
  let : MulAction H {v // π v = a} := fibreMulAction π hπ a
  let : MulAction H {v // π v = b} := fibreMulAction π hπ b
  have hta : ∀ x y : {v // π v = a}, ∃ g : H, g • x = y := by
    intro x y
    obtain ⟨g, hg⟩ := ht x.val y.val (x.property.trans y.property.symm)
    exact ⟨g, Subtype.ext hg⟩
  have htb : ∀ x y : {v // π v = b}, ∃ g : H, g • x = y := by
    intro x y
    obtain ⟨g, hg⟩ := ht x.val y.val (x.property.trans y.property.symm)
    exact ⟨g, Subtype.ext hg⟩
  exact invariant_relation_majorities hta htb m (hsize a) (hsize b)
    (fun x y => ReachWithin D u x.val y.val)
    (fun g x y => reachWithin_invariant D hD g u x.val y.val) h

/-- Heavy reachability is invariant under an equivariant automorphism action. -/
theorem heavyReach_invariant {G V W : Type*} [Group G] [Fintype V]
    [DecidableEq W] [MulAction G V] [MulAction G W] (D : Digraph V) (π : V → W)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y) (u m : ℕ) :
    ∀ (g : G) a b, HeavyReach D π u m (g • a) (g • b) ↔ HeavyReach D π u m a b := by
  have forward : ∀ (g : G) a b, HeavyReach D π u m a b →
      HeavyReach D π u m (g • a) (g • b) := by
    intro g a b h
    obtain ⟨x, hx⟩ := h
    let e := equivariant_fibre_equiv π hπ g b
    have hc : (Finset.univ.filter (fun y : {v // π v = b} => ReachWithin D u x.val y.val)).card =
        (Finset.univ.filter (fun y : {v // π v = g • b} => ReachWithin D u (g • x.val) y.val)).card := by
      apply Finset.card_bijective e e.bijective
      intro y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change ReachWithin D u x.val y.val ↔ ReachWithin D u (g • x.val) (g • y.val)
      exact (reachWithin_invariant D hD g u x.val y.val).symm
    refine ⟨⟨g • x.val, by rw [hπ, x.property]⟩, ?_⟩
    rw [← hc]
    exact hx
  intro g a b
  constructor
  · intro h
    simpa only [inv_smul_smul] using forward g⁻¹ _ _ h
  · exact forward g a b

/-- An actual quotient arc has a perfect matching between its orbit fibres. -/
theorem orbit_arc_matching {H V W : Type*} [Group H] [Fintype V]
    [DecidableEq W] [MulAction H V] (D : Digraph V) (π : V → W)
    (hπ : ∀ (g : H) x, π (g • x) = π x)
    (hD : ∀ (g : H) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y, π x = π y → ∃ g : H, g • x = y)
    (hc : ∀ a b, Fintype.card {x // π x = a} = Fintype.card {x // π x = b})
    {a b : W} (hab : QuotientDigraph D π a b) :
    ∃ F : {x // π x = a} ≃ {x // π x = b}, ∀ x, D x.val (F x).val := by
  let : MulAction H {v // π v = a} := fibreMulAction π hπ a
  let : MulAction H {v // π v = b} := fibreMulAction π hπ b
  have hta : ∀ x y : {v // π v = a}, ∃ g : H, g • x = y := by
    intro x y
    obtain ⟨g, hg⟩ := ht x.val y.val (x.property.trans y.property.symm)
    exact ⟨g, Subtype.ext hg⟩
  have htb : ∀ x y : {v // π v = b}, ∃ g : H, g • x = y := by
    intro x y
    obtain ⟨g, hg⟩ := ht x.val y.val (x.property.trans y.property.symm)
    exact ⟨g, Subtype.ext hg⟩
  obtain ⟨_, x, y, hx, hy, hxy⟩ := hab
  have hne : ∃ (x : {v // π v = a}) (y : {v // π v = b}), D x.val y.val :=
    ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩
  obtain ⟨_, _, _, _, F, hF⟩ := symmetry_matching hta htb (hc a b)
    (fun x y => D x.val y.val) hne (fun g x y => hD g x.val y.val)
  exact ⟨F, hF⟩

end DirectedCycles
