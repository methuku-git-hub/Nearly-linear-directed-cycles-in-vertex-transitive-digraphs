module

public import DirectedCycles.FiniteStructure
public import DirectedCycles.ActionBallCardinality
public import DirectedCycles.ActionBallPaths
public import DirectedCycles.PolynomialCrossing

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The finite small-tripling structural assertion. This proposition is
not assumed by any unconditional theorem and has not yet been proved. -/
def FiniteTriplingStructure : Prop :=
  ∀ K : ℕ, 1 ≤ K → ∃ B r c I C N₀ : ℕ, 1 ≤ B ∧ 1 ≤ C ∧ 1 ≤ N₀ ∧
    ∀ (G V : Type) [Group G] [Finite G] [Finite V] [MulAction G V]
      (R : Digraph V) (e : V),
      (∀ x y, R x y → R y x) →
      (∀ g : G, ∀ x y, R (g • x) (g • y) ↔ R x y) →
      (∀ x y : V, ∃ g : G, g • x = y) → StronglyConnected R →
      ∀ m : ℕ, N₀ ≤ m →
      Nat.card (relationBall R e (3*m)) ≤ K*Nat.card (relationBall R e m) →
      ∃ (H : Subgroup G) (hH : H.Normal),
        letI := hH
        (H : Set G) ⊆ actionStepSet R e ^ (C*m) ∧
        (letI := normalOrbitAction (V := V) H
         let Ω := Quotient (MulAction.orbitRel H V)
         let A := PermutationImage G Ω
         (∀ x : Ω, Nat.card (MulAction.stabilizer A x) ≤ B) ∧
         ∃ (N : Subgroup A) (_hN : N.Normal) (_hNil : Group.IsNilpotent N),
           Group.rank N ≤ r ∧ Group.nilpotencyClass N ≤ c ∧ N.index ≤ I)

/-- The finite polynomial-growth specialization follows from the explicit
small-tripling assertion. The latter is proved by finite_tripling_structure in FiniteStructuralTheorems. -/
theorem finite_structure_of_tripling (hstructure : FiniteTriplingStructure) :
    FiniteStructuralInput := by
  intro lam hlam _hlam1
  obtain ⟨K,hK,hscale⟩ := eventual_small_tripling_scale lam hlam
  obtain ⟨B,r,c,I,C,N₀,hB,hC,hN₀,hstructure⟩ := hstructure K hK
  obtain ⟨n₀,hn₀⟩ := hscale N₀ C hN₀ hC
  refine ⟨B,r,c,I,max n₀ 1,hB,?_⟩
  intro n hn X hl hc ht
  have hn1 : 1 ≤ n := (le_max_right n₀ 1).trans hn
  let e : Fin n := ⟨0,by omega⟩
  let G := automorphismGroup X
  let R : Digraph (Fin n) := fun x y => X x y ∨ X y x
  have hsym : ∀ x y, R x y → R y x := fun _ _ h => h.elim Or.inr Or.inl
  have hinv : ∀ g : G, ∀ x y, R (g • x) (g • y) ↔ R x y := by
    intro g x y
    exact or_congr (automorphismGroup_invariant X g x y) (automorphismGroup_invariant X g y x)
  have htrans : ∀ x y : Fin n, ∃ g : G, g • x = y := automorphismGroup_transitive X ht
  have hconn : StronglyConnected R := hc
  let f := fun t => Nat.card (relationBall R e t)
  have hf : ∀ t, 1 ≤ f t ∧ f t ≤ n := by
    intro t
    simpa only [Nat.card_fin] using relationBall_card_bounds R e t
  obtain ⟨m,hm,hrad,htrip⟩ := hn₀ n ((le_max_left n₀ 1).trans hn) f hf
  obtain ⟨H,hH,hball,hquot⟩ := hstructure G (Fin n) R e hsym hinv htrans hconn m hm htrip
  let : H.Normal := hH
  refine ⟨H,hH,?_,hquot⟩
  intro x y hxy
  obtain ⟨P,hP⟩ := normal_subgroup_ball_short_paths R e hinv htrans H (C*m)
    (by have := hN₀.trans hm; nlinarith) hball x y hxy
  refine ⟨P,?_⟩
  exact (show (P.length : ℝ) ≤ C*m by exact_mod_cast hP).trans hrad

end DirectedCycles
