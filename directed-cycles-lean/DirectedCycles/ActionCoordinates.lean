module

public import DirectedCycles.FreeQuotient

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem free_action_smul_injective {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (x : V) :
    Function.Injective (fun g : G => g • x) := by
  intro g h he
  change g • x = h • x at he
  have hf : (g⁻¹*h) • x = x := by rw [mul_smul,← he,inv_smul_smul]
  exact inv_mul_eq_one.mp (hfree _ x hf)

theorem orbitProjection_smul {G V : Type*} [Group G] [MulAction G V] (g : G) (x : V) :
    (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel G V)) = Quotient.mk'' x :=
  Quotient.sound (MulAction.mem_orbit x g)

/-- Choosing one representative per orbit gives genuine group coordinates
for every semiregular action. -/
noncomputable def freeActionCoordinates {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) :
    G × Quotient (MulAction.orbitRel G V) ≃ V :=
  Equiv.ofBijective (fun p => p.1 • p.2.out) (by
    constructor
    · rintro ⟨g,i⟩ ⟨h,j⟩ he
      have hij : i = j := by
        have hi := (orbitProjection_smul g i.out).trans (Quotient.out_eq i)
        have hj := (orbitProjection_smul h j.out).trans (Quotient.out_eq j)
        exact hi.symm.trans ((congrArg Quotient.mk'' he).trans hj)
      subst j
      have hgh := free_action_smul_injective hfree i.out he
      exact Prod.ext hgh rfl
    · intro x
      let q : Quotient (MulAction.orbitRel G V) := Quotient.mk'' x
      have he : (Quotient.mk'' x : Quotient (MulAction.orbitRel G V)) = Quotient.mk'' q.out :=
        (Quotient.out_eq q).symm
      obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
      exact ⟨(g,q),hg⟩)

theorem freeActionCoordinates_smul {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1)
    (g h : G) (i : Quotient (MulAction.orbitRel G V)) :
    freeActionCoordinates hfree (g*h,i) = g • freeActionCoordinates hfree (h,i) :=
  mul_smul g h i.out

/-- The exact semiregular counting identity, with no transitivity assumption. -/
theorem free_action_cardinality {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) :
    Nat.card V = Nat.card G*Nat.card (Quotient (MulAction.orbitRel G V)) := by
  rw [← Nat.card_congr (freeActionCoordinates hfree),Nat.card_prod]

/-- All labelled orbit arcs, including within-orbit arcs, are retained. -/
def VoltageDigraph {G I : Type*} [Group G] (S : I → I → Set G) : Digraph (G × I) :=
  fun x y => ∃ a ∈ S x.2 y.2, y.1 = x.1*a

def orbitArcLabels {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (D : Digraph V)
    (i j : Quotient (MulAction.orbitRel G V)) : Set G :=
  {a | D (freeActionCoordinates hfree (1,i)) (freeActionCoordinates hfree (a,j))}

/-- The labelled voltage graph is exactly the original invariant digraph
in the chosen coordinates. -/
theorem free_action_voltage_arc {G V : Type*} [Group G] [MulAction G V]
    (hfree : ∀ g : G, ∀ x : V, g • x = x → g = 1) (D : Digraph V)
    (hD : ∀ g : G, ∀ x y : V, D (g • x) (g • y) ↔ D x y)
    (x y : G × Quotient (MulAction.orbitRel G V)) :
    VoltageDigraph (orbitArcLabels hfree D) x y ↔
      D (freeActionCoordinates hfree x) (freeActionCoordinates hfree y) := by
  let e := freeActionCoordinates hfree
  constructor
  · rintro ⟨a,ha,he⟩
    have h := (hD x.1 (e (1,x.2)) (e (a,y.2))).mpr ha
    rw [← freeActionCoordinates_smul,← freeActionCoordinates_smul,mul_one,← he] at h
    exact h
  · intro h
    refine ⟨x.1⁻¹*y.1,?_,by group⟩
    have hh := (hD x.1⁻¹ (e x) (e y)).mpr h
    change D (x.1⁻¹ • e (x.1,x.2)) (x.1⁻¹ • e (y.1,y.2)) at hh
    rw [← freeActionCoordinates_smul,← freeActionCoordinates_smul,inv_mul_cancel] at hh
    exact hh

end DirectedCycles
