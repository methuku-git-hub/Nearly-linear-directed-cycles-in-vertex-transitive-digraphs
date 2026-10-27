module

public import DirectedCycles.OrbitRouteSampler
public import DirectedCycles.UniformMarginals
public import DirectedCycles.PathSupports
public import DirectedCycles.Shortening

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- At each tour position, choose its endpoint and its private group seed. -/
abbrev EndpointSeed {G V W : Type*} (π : V → W) {n : ℕ} (A : Fin n → W) (i : Fin n) :=
  {x // π x = A i} × G

noncomputable def cyclicSampledPath {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] {D : Digraph V} (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y)
    {n : ℕ} (A : Fin n → W) (hA : ∀ i, Q (A i) (A (finRotate n i)))
    (i : Fin n) (ω : ∀ j, EndpointSeed (G := G) π A j) : List V :=
  orbitRoute Q π hQ hπ base (A i) (A (finRotate n i)) (hA i)
    (ω i).1 (ω (finRotate n i)).1 (ω i).2

theorem cyclicSampledPath_depends {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] {D : Digraph V} (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y)
    {n : ℕ} (A : Fin n → W) (hA : ∀ i, Q (A i) (A (finRotate n i))) (i : Fin n) :
    DependsOn (stepSupport (finRotate n) i) (cyclicSampledPath Q π hQ hπ base A hA i) := by
  intro ω ω' he
  have hi := he i (by simp [stepSupport])
  have hj := he (finRotate n i) (by simp [stepSupport])
  simp only [cyclicSampledPath, hi, hj]

theorem cyclicSampledPath_loop {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] {D : Digraph V}
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y)
    {n : ℕ} (A : Fin n → W) (hA : ∀ i, Q (A i) (A (finRotate n i)))
    (ω : ∀ j, EndpointSeed (G := G) π A j) :
    IsPathLoop D (fun i => cyclicSampledPath Q π hQ hπ base A hA i ω) := by
  constructor
  · intro i hn
    have hh := twistedRoute_head (endpoint_relation_invariant Q π hQ hπ) base
      (ω i).1.val (ω (finRotate n i)).1.val
      (by rw [(ω i).1.property, (ω (finRotate n i)).1.property]; exact hA i) (ω i).2
    change (cyclicSampledPath Q π hQ hπ base A hA i ω).head? = _ at hh
    rw [hn] at hh
    contradiction
  · intro i
    exact twistedRoute_nodup (endpoint_relation_invariant Q π hQ hπ) base
      (ω i).1.val (ω (finRotate n i)).1.val
      (by rw [(ω i).1.property, (ω (finRotate n i)).1.property]; exact hA i) (ω i).2
  · intro i
    exact twistedRoute_chain hD (endpoint_relation_invariant Q π hQ hπ) base
      (ω i).1.val (ω (finRotate n i)).1.val
      (by rw [(ω i).1.property, (ω (finRotate n i)).1.property]; exact hA i) (ω i).2
  · intro i
    simp only [cyclicSampledPath, orbitRoute, twistedRoute_last, twistedRoute_head]

theorem cyclicSampledPath_length {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] {D : Digraph V} (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y) (t : ℕ)
    (hlen : ∀ x y h, (base x y h).length ≤ t)
    {n : ℕ} (A : Fin n → W) (hA : ∀ i, Q (A i) (A (finRotate n i)))
    (i : Fin n) (ω : ∀ j, EndpointSeed (G := G) π A j) :
    (cyclicSampledPath Q π hQ hπ base A hA i ω).length ≤ t + 1 :=
  twistedRoute_length (endpoint_relation_invariant Q π hQ hπ) base t hlen
    (ω i).1.val (ω (finRotate n i)).1.val
    (by rw [(ω i).1.property, (ω (finRotate n i)).1.property]; exact hA i) (ω i).2

/-- Reorder two endpoint/seed pairs so that the unused second private seed
is a separate product factor. -/
def endpointSeedEquiv {A B G : Type*} : (A × G) × (B × G) ≃ (A × (B × G)) × G where
  toFun p := ((p.1.1, (p.2.1, p.1.2)), p.2.2)
  invFun p := ((p.1.1, p.1.2.2), (p.1.2.1, p.2))

/-- The route at a tour position has exactly the previously defined marginal
law; the proof integrates out every unused independent coordinate. -/
theorem cyclicSampledPath_marginal {G V W : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq W] [MulAction G V] [MulAction G W]
    {D : Digraph V} (Q : Digraph W) (π : V → W) (hs : Function.Surjective π)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y)
    {n : ℕ} (hn : 4 ≤ n) (A : Fin n → W) (hA : ∀ i, Q (A i) (A (finRotate n i)))
    (i : Fin n) (v : V) :
    uniformProbability (fun ω => v ∈ cyclicSampledPath Q π hQ hπ base A hA i ω) =
      orbitRouteLoad Q π hQ hπ base (A i) (A (finRotate n i)) (hA i) v := by
  let β := EndpointSeed (G := G) π A
  let : ∀ j, Nonempty (β j) := fun j =>
    let ⟨x, hx⟩ := hs (A j)
    ⟨(⟨x, hx⟩, 1)⟩
  let j := finRotate n i
  have hji : j ≠ i := by
    simpa only [Function.iterate_one] using
      rotate_iterate_ne_self (n := n) (k := 1) (by omega) (by omega) i
  let f : β i → β j → ℝ := fun x y => eventIndicator
    (v ∈ orbitRoute Q π hQ hπ base (A i) (A j) (hA i) x.1 y.1 x.2)
  change uniformAverage (fun ω : ∀ j, β j => f (ω i) (ω j)) = _
  rw [uniformAverage_two_coordinates β i j hji f]
  let F := fun z : {x // π x = A i} × ({y // π y = A j} × G) =>
    eventIndicator (v ∈ orbitRoute Q π hQ hπ base (A i) (A j) (hA i) z.1 z.2.1 z.2.2)
  calc uniformAverage (fun p : β i × β j => f p.1 p.2) =
      uniformAverage (fun p => F (endpointSeedEquiv p).1) := rfl
    _ = uniformAverage (fun p : ({x // π x = A i} × ({y // π y = A j} × G)) × G => F p.1) :=
      uniformAverage_equiv endpointSeedEquiv (fun p => F p.1)
    _ = uniformAverage F := uniformAverage_prod_left F
    _ = _ := rfl

end DirectedCycles
