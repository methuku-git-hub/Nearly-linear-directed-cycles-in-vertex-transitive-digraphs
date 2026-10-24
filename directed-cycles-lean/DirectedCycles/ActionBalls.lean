import DirectedCycles.NormalPartitions
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Vertices reachable in at most n steps; the recursion permits staying. -/
def relationBall {V : Type*} (R : Digraph V) (e : V) : ℕ → Set V
  | 0 => {e}
  | n+1 => {y | ∃ x ∈ relationBall R e n, y = x ∨ R x y}

theorem relationBall_step {V : Type*} (R : Digraph V) (e : V) (n : ℕ) :
    relationBall R e n ⊆ relationBall R e (n+1) := fun y hy => ⟨y,hy,Or.inl rfl⟩

theorem reachable_mem_relationBall {V : Type*} {R : Digraph V} {e y : V}
    (h : Reachable R e y) : ∃ n, y ∈ relationBall R e n := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | @tail y z h hyz ih =>
    obtain ⟨n,hn⟩ := ih
    exact ⟨n+1,y,hn,Or.inr hyz⟩

def actionStepSet {G V : Type*} [Group G] [MulAction G V] (R : Digraph V) (e : V) : Set G :=
  {g | g • e = e ∨ R e (g • e)}

theorem actionStepSet_one {G V : Type*} [Group G] [MulAction G V] (R : Digraph V) (e : V) :
    (1 : G) ∈ actionStepSet R e := Or.inl (one_smul G e)

/-- Positive powers of the step set are exactly the preimages of graph
balls. The positivity condition retains the entire vertex stabilizer. -/
theorem actionStepSet_pow {G V : Type*} [Group G] [MulAction G V]
    (R : Digraph V) (e : V) (hR : ∀ g : G, ∀ x y, R (g • x) (g • y) ↔ R x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (n : ℕ) (hn : 1 ≤ n) :
    actionStepSet R e ^ n = (fun g : G => g • e) ⁻¹' relationBall R e n := by
  have h : ∀ k : ℕ, ∀ g : G,
      g ∈ actionStepSet R e ^ (k+1) ↔ g • e ∈ relationBall R e (k+1) := by
    intro k
    induction k with
    | zero =>
      intro g
      rw [pow_one]
      change (g • e = e ∨ R e (g • e)) ↔ ∃ x ∈ ({e} : Set V), g • e = x ∨ R x (g • e)
      simp only [Set.mem_singleton_iff,exists_eq_left]
    | succ k ih =>
      intro g
      rw [pow_succ]
      constructor
      · rintro ⟨a,ha,b,hb,rfl⟩
        refine ⟨a • e,(ih a).mp ha,?_⟩
        rcases hb with hb | hb
        · left
          rw [mul_smul,hb]
        · right
          rw [mul_smul]
          exact (hR a e (b • e)).mpr hb
      · rintro ⟨x,hx,hg⟩
        obtain ⟨a,ha⟩ := ht e x
        refine ⟨a,(ih a).mpr (ha ▸ hx),a⁻¹*g,?_,mul_inv_cancel_left _ _⟩
        change (a⁻¹*g) • e = e ∨ R e ((a⁻¹*g) • e)
        rcases hg with hg | hg
        · left
          rw [mul_smul,hg,← ha,inv_smul_smul]
        · right
          have hh := (hR a⁻¹ x (g • e)).mpr hg
          simpa only [← ha,inv_smul_smul,mul_smul] using hh
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact Set.ext (h k)

theorem actionStepSet_generates {G V : Type*} [Group G] [MulAction G V]
    (R : Digraph V) (e : V) (hR : ∀ g : G, ∀ x y, R (g • x) (g • y) ↔ R x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (hconn : StronglyConnected R) :
    Subgroup.closure (actionStepSet R e : Set G) = ⊤ := by
  apply top_le_iff.mp
  intro g hg
  clear hg
  obtain ⟨n,hn⟩ := reachable_mem_relationBall (hconn e (g • e))
  have hmem : g ∈ actionStepSet R e ^ (n+1) := by
    rw [actionStepSet_pow R e hR ht (n+1) (by omega)]
    exact relationBall_step R e n hn
  have hsub : ∀ k, actionStepSet R e ^ k ⊆ ((Subgroup.closure (actionStepSet R e : Set G)) : Set G) := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have he : x = 1 := hx
      exact he ▸ Subgroup.one_mem _
    | succ k ih =>
      rw [pow_succ]
      rintro x ⟨a,ha,b,hb,rfl⟩
      exact Subgroup.mul_mem _ (ih ha) (Subgroup.subset_closure hb)
  exact hsub (n+1) hmem

end DirectedCycles
