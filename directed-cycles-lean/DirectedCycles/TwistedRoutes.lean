import DirectedCycles.Paths

set_option autoImplicit false
namespace DirectedCycles

/-- Randomly translating a fixed endpoint-prescribed route. The group element
is a private seed; no equivariance of the arbitrary base-route choice is assumed. -/
noncomputable def twistedRoute {G V : Type*} [Group G] [MulAction G V]
    {D E : Digraph V} (hE : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (base : ∀ x y, E x y → SimplePath D x y) (x y : V) (hxy : E x y) (g : G) : List V :=
  (base (g⁻¹ • x) (g⁻¹ • y) ((hE g⁻¹ x y).mpr hxy)).vertices.map (fun v => g • v)

theorem twistedRoute_head {G V : Type*} [Group G] [MulAction G V]
    {D E : Digraph V} (hE : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (base : ∀ x y, E x y → SimplePath D x y) (x y : V) (hxy : E x y) (g : G) :
    (twistedRoute hE base x y hxy g).head? = some x := by
  simp [twistedRoute, List.head?_map, SimplePath.head]

theorem twistedRoute_last {G V : Type*} [Group G] [MulAction G V]
    {D E : Digraph V} (hE : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (base : ∀ x y, E x y → SimplePath D x y) (x y : V) (hxy : E x y) (g : G) :
    (twistedRoute hE base x y hxy g).getLast? = some y := by
  simp [twistedRoute, List.getLast?_map, SimplePath.last]

theorem twistedRoute_nodup {G V : Type*} [Group G] [MulAction G V]
    {D E : Digraph V} (hE : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (base : ∀ x y, E x y → SimplePath D x y) (x y : V) (hxy : E x y) (g : G) :
    (twistedRoute hE base x y hxy g).Nodup :=
  (base _ _ _).nodup.map (MulAction.toPerm g).injective

theorem twistedRoute_chain {G V : Type*} [Group G] [MulAction G V]
    {D E : Digraph V} (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (hE : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (base : ∀ x y, E x y → SimplePath D x y) (x y : V) (hxy : E x y) (g : G) :
    (twistedRoute hE base x y hxy g).IsChain D := by
  unfold twistedRoute
  rw [List.isChain_map]
  exact (base _ _ _).chain.imp (fun a b hab => (hD g a b).mpr hab)

theorem twistedRoute_length {G V : Type*} [Group G] [MulAction G V]
    {D E : Digraph V} (hE : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (base : ∀ x y, E x y → SimplePath D x y) (t : ℕ)
    (hlen : ∀ x y h, (base x y h).length ≤ t) (x y : V) (hxy : E x y) (g : G) :
    (twistedRoute hE base x y hxy g).length ≤ t + 1 := by
  simp only [twistedRoute, List.length_map]
  have h := hlen (g⁻¹ • x) (g⁻¹ • y) ((hE g⁻¹ x y).mpr hxy)
  dsimp only [SimplePath.length] at h
  omega

/-- Left translation of the private seed makes the route sampler equivariant,
regardless of the fixed base-route choices. -/
theorem twistedRoute_equivariant {G V : Type*} [Group G] [MulAction G V]
    {D E : Digraph V} (hE : ∀ (g : G) x y, E (g • x) (g • y) ↔ E x y)
    (base : ∀ x y, E x y → SimplePath D x y) (x y : V) (hxy : E x y) (g h : G) :
    twistedRoute hE base (h • x) (h • y) ((hE h x y).mpr hxy) (h * g) =
      (twistedRoute hE base x y hxy g).map (fun v => h • v) := by
  have hc : ∀ {a b c d : V}, a = c → b = d → ∀ (h1 : E a b) (h2 : E c d),
      (base a b h1).vertices = (base c d h2).vertices := by
    intro a b c d ha hb h1 h2
    subst c; subst d
    rfl
  have hx : (h * g)⁻¹ • (h • x) = g⁻¹ • x := by
    rw [mul_inv_rev, mul_smul, inv_smul_smul]
  have hy : (h * g)⁻¹ • (h • y) = g⁻¹ • y := by
    rw [mul_inv_rev, mul_smul, inv_smul_smul]
  simp only [twistedRoute, mul_smul, List.map_map, Function.comp_def]
  apply congrArg (List.map (fun v => h • g • v))
  exact hc hx hy _ _


end DirectedCycles
