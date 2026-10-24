import DirectedCycles.TwistedRoutes
import DirectedCycles.UniformFinite
import DirectedCycles.NormalPartitions

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Admissibility of endpoint pairs inherits the quotient symmetry. -/
theorem endpoint_relation_invariant {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) :
    ∀ (g : G) x y, Q (π (g • x)) (π (g • y)) ↔ Q (π x) (π y) := by
  intro g x y
  rw [hπ, hπ, hQ]

/-- The actual path sample with given orbit endpoints and private group seed. -/
noncomputable def orbitRoute {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] {D : Digraph V} (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y)
    (a b : W) (hab : Q a b) (x : {x // π x = a}) (y : {y // π y = b}) (g : G) : List V :=
  twistedRoute (endpoint_relation_invariant Q π hQ hπ) base x.val y.val
    (by rw [x.property, y.property]; exact hab) g

theorem orbitRoute_equivariant {G V W : Type*} [Group G]
    [MulAction G V] [MulAction G W] {D : Digraph V} (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y)
    (a b : W) (hab : Q a b) (x : {x // π x = a}) (y : {y // π y = b}) (g h : G) :
    orbitRoute Q π hQ hπ base (h • a) (h • b) ((hQ h a b).mpr hab)
      (equivariant_fibre_equiv π hπ h a x) (equivariant_fibre_equiv π hπ h b y) (h * g) =
        (orbitRoute Q π hQ hπ base a b hab x y g).map (fun v => h • v) := by
  exact twistedRoute_equivariant (endpoint_relation_invariant Q π hQ hπ) base
    x.val y.val _ g h

/-- Marginal inclusion probability for one quotient arc, sampling both
endpoints and the private seed uniformly and independently. -/
noncomputable def orbitRouteLoad {G V W : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq W] [MulAction G V] [MulAction G W]
    {D : Digraph V} (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y)
    (a b : W) (hab : Q a b) (v : V) : ℝ :=
  uniformProbability (fun z : {x // π x = a} × ({y // π y = b} × G) =>
    v ∈ orbitRoute Q π hQ hπ base a b hab z.1 z.2.1 z.2.2)

/-- Equivariance of the marginal distribution is proved by an explicit
bijection of its finite sample space. -/
theorem orbitRouteLoad_equivariant {G V W : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq W] [MulAction G V] [MulAction G W]
    {D : Digraph V} (Q : Digraph W) (π : V → W)
    (hQ : ∀ (g : G) a b, Q (g • a) (g • b) ↔ Q a b)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x)
    (base : ∀ x y, Q (π x) (π y) → SimplePath D x y)
    (a b : W) (hab : Q a b) (v : V) (h : G) :
    orbitRouteLoad Q π hQ hπ base (h • a) (h • b) ((hQ h a b).mpr hab) (h • v) =
      orbitRouteLoad Q π hQ hπ base a b hab v := by
  let e := (equivariant_fibre_equiv π hπ h a).prodCongr
    ((equivariant_fibre_equiv π hπ h b).prodCongr (Equiv.mulLeft h))
  let A := fun z : {x // π x = h • a} × ({y // π y = h • b} × G) =>
    h • v ∈ orbitRoute Q π hQ hπ base (h • a) (h • b) ((hQ h a b).mpr hab) z.1 z.2.1 z.2.2
  change uniformProbability A = _
  rw [← uniformProbability_equiv e A]
  unfold orbitRouteLoad
  congr 1
  funext z
  apply propext
  change (h • v ∈ orbitRoute Q π hQ hπ base (h • a) (h • b) ((hQ h a b).mpr hab)
    (equivariant_fibre_equiv π hπ h a z.1) (equivariant_fibre_equiv π hπ h b z.2.1) (h * z.2.2)) ↔ _
  rw [orbitRoute_equivariant]
  constructor
  · intro hm
    obtain ⟨u, hu, huv⟩ := List.mem_map.mp hm
    have huv' : u = v := (MulAction.toPerm h).injective huv
    simpa only [huv'] using hu
  · intro hm
    exact List.mem_map.mpr ⟨v, hm, rfl⟩

end DirectedCycles
