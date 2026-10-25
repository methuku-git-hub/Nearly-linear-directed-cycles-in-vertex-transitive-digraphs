module

public import DirectedCycles.AbelianLargeRound
public import DirectedCycles.AbelianBoundedRounds
public import DirectedCycles.BaselineHamiltonian
public import DirectedCycles.SubsingletonLayers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- An explicit uniform linear constant for the abelian layer base case. The
smaller constant replaces the manuscript's unused sharper quarter bound. -/
noncomputable def abelianLayerConstant (r D : ℕ) : ℝ :=
  min (((8*D+4).factorial^r : ℕ) : ℝ)⁻¹ (1/8)

theorem abelianLayerConstant_bounds (r D : ℕ) :
    0 < abelianLayerConstant r D ∧ abelianLayerConstant r D ≤ 1/8 ∧
      abelianLayerConstant r D * (((8*D+4).factorial^r : ℕ) : ℝ) ≤ 1 := by
  have hp : (0 : ℝ) < (((8*D+4).factorial^r : ℕ) : ℝ) := by positivity
  refine ⟨lt_min (inv_pos.mpr hp) (by norm_num),min_le_right _ _,?_⟩
  have h := mul_le_mul_of_nonneg_right (min_le_left
    ((((8*D+4).factorial^r : ℕ) : ℝ)⁻¹) (1/8 : ℝ)) hp.le
  rwa [inv_mul_cancel₀ hp.ne'] at h

/-- A uniform abelian layer base case, including the exact spanning invariant
needed by the normal-closure induction. The proof uses the general round lift. -/
theorem abelian_layer_cycle_bound {G : Type*} [CommGroup G] [Finite G]
    (r D : ℕ) (hr : Group.rank G ≤ r) {T : ℕ} (hT : 2 ≤ T)
    (S : ZMod T → Set G) (hsc : StronglyConnected (CyclicLayerDigraph S)) :
    ∃ L : Cycle (CyclicLayerDigraph S),
      abelianLayerConstant r D*T*Nat.card G ≤ L.length ∧
      ((∀ p : ℕ, p.Prime → p ∣ Nat.card G → 8*D+4 < p) →
        ∀ z : ZMod T, SpansTruncation D (L.layerCoordinates z)) := by
  let : NeZero T := ⟨by omega⟩
  have hone : (1 : ZMod T) ≠ 0 := by
    intro he
    have hd : T ∣ 1 := (ZMod.natCast_eq_zero_iff 1 T).mp (by simpa only [Nat.cast_one] using he)
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  let : Nontrivial (ZMod T) := ⟨⟨1,0,hone⟩⟩
  obtain ⟨hb,hb8,hbM⟩ := abelianLayerConstant_bounds r D
  have hb1 : abelianLayerConstant r D ≤ 1 := by linarith
  rcases subsingleton_or_nontrivial G with hG | hG
  · let : Subsingleton G := hG
    obtain ⟨L,hL,hs⟩ := subsingleton_layer_hamiltonian hT S hsc
    refine ⟨L,?_,?_⟩
    · have hc : Nat.card G = 1 := Nat.card_unique
      rw [hc,Nat.cast_one,mul_one]
      have hm := mul_le_mul_of_nonneg_right hb1 (by positivity : (0 : ℝ) ≤ T)
      have hL' : (T : ℝ) ≤ L.length := by exact_mod_cast hL
      simp only [one_mul] at hm
      exact hm.trans hL'
    · intro _ z
      have he : L.layerCoordinates z = Set.univ := Set.eq_univ_of_forall (fun x => hs (x,z))
      rw [he]
      exact spansTruncation_univ D
  · let : Nontrivial G := hG
    by_cases hlarge : ∃ t ∈ layerRoundProducts S, 8*D+4 < orderOf t
    · obtain ⟨t,⟨xs,hlen,hxs,he⟩,ht⟩ := hlarge
      subst t
      by_cases hK : elementClosure xs.prod = ⊤
      · have hgen : Subgroup.zpowers xs.prod = ⊤ := by rwa [abelian_elementClosure] at hK
        obtain ⟨L,hL,hfull⟩ := generating_baseline_hamiltonian S xs hlen hxs hgen
        refine ⟨L,?_,?_⟩
        · rw [hL,Nat.cast_mul]
          have hm := mul_le_mul_of_nonneg_right hb1 (by positivity : (0 : ℝ) ≤ (T : ℝ)*Nat.card G)
          simpa only [one_mul,mul_assoc] using hm
        · intro _ z
          rw [hfull]
          exact spansTruncation_univ D
      · obtain ⟨L,hL,hspan⟩ := abelian_large_round_cycle S hsc xs hlen hxs D ht hK
        refine ⟨L,?_,hspan⟩
        have hm := mul_le_mul_of_nonneg_right hb8 (by positivity : (0 : ℝ) ≤ (T : ℝ)*Nat.card G)
        have heq : abelianLayerConstant r D*T*Nat.card G ≤ (T : ℝ)*Nat.card G/8 := by nlinarith
        exact heq.trans hL
    · have hord : ∀ t ∈ layerRoundProducts S, orderOf t ≤ 8*D+4 := by
        intro t ht
        by_contra he
        exact hlarge ⟨t,ht,by omega⟩
      have hcard := abelian_card_of_bounded_round_orders S hsc (8*D+4) r hr hord
      obtain ⟨L,hL⟩ := stronglyConnected_layer_cycle hT S hsc
      refine ⟨L,?_,?_⟩
      · have hc : (Nat.card G : ℝ) ≤ (((8*D+4).factorial^r : ℕ) : ℝ) := by exact_mod_cast hcard
        have hbc := (mul_le_mul_of_nonneg_left hc hb.le).trans hbM
        have hscaled := mul_le_mul_of_nonneg_left hbc (by positivity : (0 : ℝ) ≤ T)
        have hL' : (T : ℝ) ≤ L.length := by exact_mod_cast hL
        nlinarith
      · intro hp
        obtain ⟨t,ht,ht1⟩ := generating_set_nonidentity (layerRoundProducts S)
          (cyclicLayer_rounds_generate S hsc)
        exact False.elim (not_lt_of_ge (hord t ht) (order_above_prime_cutoff (8*D+4) hp t ht1))

end DirectedCycles
