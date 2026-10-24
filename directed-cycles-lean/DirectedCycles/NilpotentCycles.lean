import DirectedCycles.NilpotentInduction
import DirectedCycles.SingleLayerCycles

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- The manuscript permits a loop only when the coordinate group and layer
set are both singletons. This disjunction states that exception explicitly. -/
def LayerCycleOrTrivialLoop {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (bound : ℝ) : Prop :=
  (∃ C : Cycle (CyclicLayerDigraph S), bound ≤ C.length) ∨
    (Nat.card G = 1 ∧ T = 1 ∧ ∃ x : G × ZMod T, CyclicLayerDigraph S x x ∧ bound ≤ 1)

/-- Manuscript Theorem 6.1, with the exceptional singleton loop stated
separately. The constant precedes the group, labels, and number of layers. -/
theorem nilpotent_cycle_theorem (r c : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℝ, 0 < b ∧ ∀ (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G],
      Group.rank G ≤ r → Group.nilpotencyClass G ≤ c →
      (Nontrivial G → ∀ S : Set G, Subgroup.closure S = ⊤ →
        ∃ C : Cycle (CayleyDigraph S), b*(Nat.card G : ℝ)^(1-eps) ≤ C.length) ∧
      (∀ T : ℕ, 1 ≤ T → ∀ S : ZMod T → Set G, (∀ z, (S z).Nonempty) →
        StronglyConnected (CyclicLayerDigraph S) →
        LayerCycleOrTrivialLoop S (b*T*(Nat.card G : ℝ)^(1-eps))) := by
  obtain ⟨b,hb,hbounds⟩ := nilpotent_spanning_bounds c r c le_rfl eps heps
  let b' := min b 1
  have hb' : 0 < b' := lt_min hb (by norm_num)
  have hb'le : b' ≤ b := min_le_left _ _
  have hb'1 : b' ≤ 1 := min_le_right _ _
  refine ⟨b',hb',?_⟩
  intro G _ _ _ hr hc
  have hq := ((hbounds G hr hc).1).weaken hb.le hb'le le_rfl
  have hl := ((hbounds G hr hc).2).weaken hb.le hb'le le_rfl
  constructor
  · intro hnt S hS
    obtain ⟨C,hC,_⟩ := hq hnt S hS
    exact ⟨C,hC⟩
  · intro T hT S hS hsc
    by_cases hT2 : 2 ≤ T
    · obtain ⟨C,hC,_⟩ := hl T hT2 S hS hsc
      exact Or.inl ⟨C,hC⟩
    · have hT1 : T = 1 := by omega
      subst T
      rcases subsingleton_or_nontrivial G with hG | hG
      · let : Subsingleton G := hG
        have hcG : Nat.card G = 1 := Nat.card_unique
        apply Or.inr
        refine ⟨hcG,rfl,(1,0),?_,?_⟩
        · obtain ⟨a,ha⟩ := hS 0
          exact ⟨Subsingleton.elim _ _,a,ha,Subsingleton.elim _ _⟩
        · simpa only [hcG,Nat.cast_one,mul_one,Real.one_rpow] using hb'1
      · let : Nontrivial G := hG
        obtain ⟨C,hC,_⟩ := one_layer_cycle_from_cayley (c+1) b' eps hq S hsc
        exact Or.inl ⟨C,by simpa only [Nat.cast_one,mul_one] using hC⟩

end DirectedCycles
