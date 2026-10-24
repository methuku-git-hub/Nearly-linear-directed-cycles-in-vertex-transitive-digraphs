import DirectedCycles.OrbitRouteSampler
import DirectedCycles.CollisionLoads
import DirectedCycles.EulerSequence

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Transitive invariance turns a total mass estimate into a pointwise load
bound. The index permutations are explicit bijections. -/
theorem transitive_family_load_bound {G V A : Type*} [Group G] [Fintype V] [Fintype A]
    [MulAction G V] (load : A → V → ℝ) (reindex : G → Equiv.Perm A)
    (he : ∀ (g : G) a v, load (reindex g a) (g • v) = load a v)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (T : ℝ) (hmass : ∀ a, (∑ v, load a v) ≤ T) (v : V) :
    (∑ a, load a v) ≤ (Fintype.card A : ℝ) * T / Fintype.card V := by
  let S : V → ℝ := fun x => ∑ a, load a x
  have hconst : ∀ w, S w = S v := by
    intro w
    obtain ⟨g, rfl⟩ := ht v w
    calc S (g • v) = ∑ a, load (reindex g a) (g • v) :=
           (Equiv.sum_comp (reindex g) (fun a => load a (g • v))).symm
         _ = S v := by simp only [he, S]
  have htot : (Fintype.card V : ℝ) * S v ≤ (Fintype.card A : ℝ) * T := by
    calc (Fintype.card V : ℝ) * S v = ∑ w, S w := by simp [hconst]
         _ = ∑ a, ∑ w, load a w := Finset.sum_comm
         _ ≤ ∑ _a : A, T := Finset.sum_le_sum (fun a _ => hmass a)
         _ = (Fintype.card A : ℝ) * T := by simp
  have hv : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨v⟩
  apply (le_div_iff₀ hv).mpr
  simpa only [mul_comm] using htot

/-- The induced permutation of quotient arcs. -/
def arcEquiv {G W : Type*} [Group G] [MulAction G W] (Q : Digraph W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b) (g : G) :
    Equiv.Perm {p : W × W // Q p.1 p.2} :=
  ((MulAction.toPerm g : Equiv.Perm W).prodCongr (MulAction.toPerm g)).subtypeEquiv
    (fun p => (hQ g p.1 p.2).symm)

theorem card_arc_type_regular {W : Type*} [Fintype W] (Q : Digraph W) (d : ℕ)
    (hd : ∀ a, (Finset.univ.filter (Q a)).card = d) :
    Fintype.card {p : W × W // Q p.1 p.2} = Fintype.card W * d := by
  rw [Fintype.card_subtype]
  exact arcSet_card_regular Q d hd

/-- Every marginal route distribution has total vertex load at most `t+1`. -/
theorem orbitRouteLoad_mass {G V W : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq W] [MulAction G V] [MulAction G W]
    {D : Digraph V} (Q : Digraph W) (π : V → W) (hs : Function.Surjective π)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y) (t : ℕ)
    (hlen : ∀ x y h, (base x y h).length ≤ t) (a b : W) (hab : Q a b) :
    (∑ v, orbitRouteLoad Q π hQ hπ base a b hab v) ≤ (t : ℝ) + 1 := by
  let : Nonempty {x // π x = a} := (hs a).elim (fun x hx => ⟨⟨x, hx⟩⟩)
  let : Nonempty {x // π x = b} := (hs b).elim (fun x hx => ⟨⟨x, hx⟩⟩)
  apply path_vertex_load_sum
  rintro ⟨x, y, g⟩
  have hh := twistedRoute_length (endpoint_relation_invariant Q π hQ hπ) base t hlen
    x.val y.val (by rw [x.property, y.property]; exact hab) g
  exact_mod_cast hh

/-- The complete equivariant arc-family load estimate, before repeating the
Euler tour. Its only route input is the actual short base-route family. -/
theorem orbitRouteLoad_global {G V W : Type*} [Group G] [Fintype G]
    [Fintype V] [Fintype W] [DecidableEq W] [MulAction G V] [MulAction G W]
    {D : Digraph V} (Q : Digraph W) (π : V → W) (hs : Function.Surjective π)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y) (t d m : ℕ)
    (hlen : ∀ x y h, (base x y h).length ≤ t)
    (hdegree : ∀ a, (Finset.univ.filter (Q a)).card = d)
    (hm : ∀ a, Fintype.card {x // π x = a} = m) (hmpos : 0 < m) (v : V) :
    (∑ e : {p : W × W // Q p.1 p.2}, orbitRouteLoad Q π hQ hπ base e.val.1 e.val.2 e.property v) ≤
      (d : ℝ) * (t + 1 : ℝ) / m := by
  let load : {p : W × W // Q p.1 p.2} → V → ℝ :=
    fun e v => orbitRouteLoad Q π hQ hπ base e.val.1 e.val.2 e.property v
  have he : ∀ (g : G) e v, load (arcEquiv Q hQ g e) (g • v) = load e v := by
    intro g e v
    exact orbitRouteLoad_equivariant Q π hQ hπ base e.val.1 e.val.2 e.property v g
  have hb := transitive_family_load_bound load (arcEquiv Q hQ) he ht ((t : ℝ) + 1)
    (fun e => orbitRouteLoad_mass Q π hs hQ hπ base t hlen e.val.1 e.val.2 e.property) v
  rw [card_arc_type_regular Q d hdegree, card_eq_quotient_mul_fibre π m hm] at hb
  have hq : (Fintype.card W : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨π v⟩).ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hr : ((Fintype.card W * d : ℕ) : ℝ) * (t + 1 : ℝ) /
      ((Fintype.card W * m : ℕ) : ℝ) = (d : ℝ) * (t + 1 : ℝ) / m := by
    push_cast
    field_simp
  simpa only [hr] using hb

end DirectedCycles
