module

public import DirectedCycles.AbelianCycleLift
public import DirectedCycles.AbelianCayleyCycle
public import DirectedCycles.RoundSpanning
public import DirectedCycles.PrimeCutoffOrders

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem SpansTruncation.mono {G : Type*} [Group G] {D : ℕ} {E F : Set G}
    (hE : SpansTruncation D E) (hEF : E ⊆ F) : SpansTruncation D F := by
  apply top_le_iff.mp
  rw [← hE]
  exact AddSubgroup.closure_mono (Set.image_mono hEF)

/-- A large-order baseline with proper normal closure gives a linear layer
cycle in the abelian case, with the spanning invariant under the prime cutoff. -/
theorem abelian_large_round_cycle {G : Type*} [CommGroup G] [Finite G]
    {T : ℕ} [NeZero T] (S : ZMod T → Set G)
    (hsc : StronglyConnected (CyclicLayerDigraph S)) (xs : List G)
    (hlen : xs.length = T) (hxs : LayerWord S 0 xs)
    (D : ℕ) (horder : 8*D+4 < orderOf xs.prod)
    (hproper : elementClosure xs.prod ≠ ⊤) :
    ∃ L : Cycle (CyclicLayerDigraph S), (T : ℝ)*Nat.card G/8 ≤ L.length ∧
      ((∀ p : ℕ, p.Prime → p ∣ Nat.card G → 8*D+4 < p) →
        ∀ z : ZMod T, SpansTruncation D (L.layerCoordinates z)) := by
  let a := xs.prod
  let K := elementClosure a
  let q := QuotientGroup.mk' K
  let A := singleRoundProducts S xs
  let : Nontrivial (G ⧸ K) := QuotientGroup.nontrivial_iff.mpr hproper
  have hA : Subgroup.closure A = ⊤ := by
    rw [singleRoundProducts_generate S xs hlen hxs,cyclicLayer_rounds_generate S hsc]
  have hqA : Subgroup.closure (q '' A) = ⊤ := by
    rw [← MonoidHom.map_closure,hA,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  obtain ⟨Q,hQ,hQspan⟩ := abelian_cayley_cycle (q '' A) hqA
  have ha : a ∈ A := ⟨xs,Or.inl rfl,hxs,rfl⟩
  obtain ⟨C,hC,hCa,hspan⟩ := abelian_cycle_lift a A ha D horder Q
  obtain ⟨L,hL,hLspan⟩ := expand_cycle_into_rounds_spanning S xs hlen hxs C hCa
  have hKcard : Nat.card K = orderOf a := by
    change Nat.card (elementClosure a) = orderOf a
    rw [abelian_elementClosure,Nat.card_zpowers]
  have hG : Nat.card G = Nat.card (G ⧸ K)*orderOf a := by
    have he := K.index_mul_card
    rw [Subgroup.index_eq_card,hKcard] at he
    exact he.symm
  have hCreal : (Nat.card G : ℝ)/8 ≤ C.length := by
    have hGreal : (Nat.card G : ℝ) = (Nat.card (G ⧸ K) : ℝ)*orderOf a := by exact_mod_cast hG
    have hbound := mul_le_mul_of_nonneg_right hQ (by positivity : (0 : ℝ) ≤ orderOf a)
    nlinarith
  refine ⟨L,?_,?_⟩
  · have hscaled := mul_le_mul_of_nonneg_left hCreal (by positivity : (0 : ℝ) ≤ T)
    rw [hL,Nat.cast_mul]
    nlinarith
  · intro hp
    apply hLspan D
    apply hspan
    have hdiv : Nat.card (G ⧸ K) ∣ Nat.card G := ⟨orderOf a,hG⟩
    have hQprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (G ⧸ K) → 8*D+4 < p :=
      fun p hpr hpd => hp p hpr (hpd.trans hdiv)
    apply (hQspan D hQprime).mono
    intro x hx
    exact List.mem_ofFn.mp ((List.dropLast_sublist _).subset hx)

end DirectedCycles
