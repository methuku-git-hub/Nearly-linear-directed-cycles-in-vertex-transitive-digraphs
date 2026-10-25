module

public import DirectedCycles.OrbitCycleWalk

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem freeActionCoordinates_orbit {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1)
    (p : G × Quotient (MulAction.orbitRel G V)) :
    (Quotient.mk'' (freeActionCoordinates hfree p) : Quotient (MulAction.orbitRel G V)) = p.2 :=
  (orbitProjection_smul p.1 p.2.out).trans (Quotient.out_eq p.2)

theorem freeActionCoordinates_symm_orbit {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (x : V) :
    ((freeActionCoordinates hfree).symm x).2 = (Quotient.mk'' x : Quotient (MulAction.orbitRel G V)) := by
  have h := freeActionCoordinates_orbit hfree ((freeActionCoordinates hfree).symm x)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem freeActionCoordinates_symm_smul {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (g : G) (x : V) :
    (freeActionCoordinates hfree).symm (g • x) =
      (g*((freeActionCoordinates hfree).symm x).1,((freeActionCoordinates hfree).symm x).2) := by
  apply (freeActionCoordinates hfree).injective
  rw [Equiv.apply_symm_apply,freeActionCoordinates_smul,Equiv.apply_symm_apply]

theorem free_action_voltage_stronglyConnected {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (D : Digraph V)
    (hD : ∀ g : G, ∀ x y : V, D (g • x) (g • y) ↔ D x y)
    (hsc : StronglyConnected D) : StronglyConnected (VoltageDigraph (orbitArcLabels hfree D)) := by
  let e := freeActionCoordinates hfree
  apply stronglyConnected_image e.symm e.symm.surjective _ hsc
  intro x y h
  apply (free_action_voltage_arc hfree D hD (e.symm x) (e.symm y)).mpr
  simpa only [e,Equiv.apply_symm_apply] using h

/-- A walk in an action graph whose orbit projection is a simple cycle. -/
structure ActionOrbitCycleWalk (G : Type*) {V : Type*} [Group G] [MulAction G V]
    (D : Digraph V) (a : G) where
  length : ℕ
  two_le : 2 ≤ length
  point : Fin (length+1) → V
  index_injective : Function.Injective (fun i : Fin length =>
    (Quotient.mk'' (point i.castSucc) : Quotient (MulAction.orbitRel G V)))
  step : ∀ i : Fin length, D (point i.castSucc) (point i.succ)
  closes : point (Fin.last length) = a • point 0

noncomputable def ActionOrbitCycleWalk.toVoltageWalk {G V : Type*} [Group G] [MulAction G V]
    {D : Digraph V} {a : G} (W : ActionOrbitCycleWalk G D a)
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1)
    (hD : ∀ g : G, ∀ x y : V, D (g • x) (g • y) ↔ D x y) :
    OrbitCycleWalk (VoltageDigraph (orbitArcLabels hfree D)) a where
  length := W.length
  two_le := W.two_le
  point i := (freeActionCoordinates hfree).symm (W.point i)
  index_injective := by
    intro i j he
    simp only [freeActionCoordinates_symm_orbit] at he
    exact W.index_injective he
  step i := by
    apply (free_action_voltage_arc hfree D hD _ _).mpr
    simpa only [Equiv.apply_symm_apply] using W.step i
  closes := by rw [W.closes,freeActionCoordinates_symm_smul]

end DirectedCycles
