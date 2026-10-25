module

public import DirectedCycles.ReturnLiftDensity
public import DirectedCycles.SemiregularReturnLifting
public import DirectedCycles.NilpotentUniformBounds
public import DirectedCycles.LowerClassInputs
public import DirectedCycles.DensityPowerArithmetic

@[expose] public section

set_option autoImplicit false
universe u v
namespace DirectedCycles

/-- The large-return case of Theorem 3.7, with a constant independent of
the group, action, orbit count, and selected orbit walk. -/
theorem large_return_cycle_bound (r c : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℝ, 0 < b ∧ ∀ (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G]
      (V : Type v) [Finite V] [MulAction G V],
      ∀ X : Digraph V, (∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y) →
      (∀ g : G, ∀ x : V, g • x = x → g = 1) → StronglyConnected X →
      Group.rank G ≤ r → Group.nilpotencyClass G ≤ c →
      ∀ a : G, ∀ _W : ActionOrbitCycleWalk G X a, elementClosure a ≠ ⊤ →
      8*(Nat.card (Quotient (MulAction.orbitRel G V))+1)*((c+1)+1) <
        orderOf (QuotientGroup.mk' (elementCommutators a) a) →
      ∃ L : Cycle X, b*(Nat.card G : ℝ)^(1-eps) ≤ L.length := by
  let k := auxiliaryIndexExponent r c c+1
  have hk : (0 : ℝ) < auxiliaryIndexExponent r c c+1 := by positivity
  let eta := eps/(auxiliaryIndexExponent r c c+1)
  have heta : 0 < eta := div_pos heps hk
  obtain ⟨bq,hbq,hq⟩ := nilpotent_cycle_theorem.{u} r c eta heta
  obtain ⟨bl,hbl,hl⟩ := nilpotent_uniform_layer_bound.{u} (∑ i ∈ Finset.range c,r^(i+1)) (c/2) eps heps
  let d := bl/(8*(auxiliaryIndexConstant r c c : ℝ))
  have hd : 0 < d := by
    have hJ : (0 : ℝ) < auxiliaryIndexConstant r c c := by exact_mod_cast auxiliaryIndexConstant_pos r c c
    exact div_pos hbl (by positivity)
  refine ⟨d*bq^k,mul_pos hd (pow_pos hbq k),?_⟩
  intro G _ _ _ V _ _ X hX hfree hsc hr hc a W hproper hh
  let K := elementClosure a
  let B := elementCommutators a
  let : Nontrivial (G ⧸ K) := QuotientGroup.nontrivial_iff.mpr hproper
  obtain ⟨S,_hS,hconn,hcon⟩ := semiregular_return_lifting X hX hfree hsc a W r c c hr hc le_rfl hh
  have hrQ : Group.rank (G ⧸ K) ≤ r :=
    (Group.rank_le_of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)).trans hr
  have hcQ : Group.nilpotencyClass (G ⧸ K) ≤ c := (Group.nilpotencyClass_quotient_le K).trans hc
  obtain ⟨C,hC⟩ := (hq (G ⧸ K) hrQ hcQ).1 inferInstance _
    (cayley_stronglyConnected_generates _ hconn)
  obtain ⟨R⟩ := hcon C
  have hsub : ∀ U : Subgroup B, LayerCycleLowerBound U bl eps := by
    intro U
    obtain ⟨hrU,hcU⟩ := elementCommutators_subgroup_bounds a r c hr hc U
    exact hl U hrU hcU
  obtain ⟨L,hL⟩ := R.density_bound bl eps hbl heps.le hsub
  refine ⟨L,?_⟩
  have hN : (0 : ℝ) < Nat.card (G ⧸ K) := by exact_mod_cast (Nat.card_pos (α := G ⧸ K))
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  have hB : (1 : ℝ) ≤ Nat.card B := by exact_mod_cast (Nat.card_pos (α := B))
  let h := Nat.card (elementClosure a ⧸ B.subgroupOf (elementClosure a))
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Nat.card_pos (α := elementClosure a ⧸ B.subgroupOf (elementClosure a)))
  have hcard : (Nat.card G : ℝ) = (Nat.card (G ⧸ K) : ℝ)*h*Nat.card B := by
    exact_mod_cast elementClosure_card_factorization a
  have hkcast : (k : ℝ) = auxiliaryIndexExponent r c c+1 := by simp only [k,Nat.cast_add,Nat.cast_one]
  have he : (k : ℝ)*eta = eps := by dsimp only [eta]; rw [hkcast]; field_simp
  have hCdens := (length_bound_iff_density_bound bq _ eta C.length hN).mp hC
  have hcalc := large_kernel_density bq d (Nat.card (G ⧸ K)) h (Nat.card B) (Nat.card G)
    eta eps C.length ((L.length : ℝ)/Nat.card G) k hbq.le hd.le hN hh1 hB hcard heps.le
    (by rw [he]) hCdens hL
  rw [he] at hcalc
  exact (length_bound_iff_density_bound (d*bq^k) _ eps L.length hG).mpr hcalc

end DirectedCycles
