module

public import DirectedCycles.CyclicLayerWords
public import DirectedCycles.StrongCycleExistence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A cycle whose phase advances by one has length divisible by the number
of phases. The sum around the cycle telescopes exactly. -/
theorem Cycle.phase_length_dvd {V : Type*} {D : Digraph V} (C : Cycle D)
    (T : ℕ) (phase : V → ZMod T)
    (h : ∀ x y, D x y → phase y = phase x+1) : T ∣ C.length := by
  have hs : (∑ i : Fin C.length, phase (C.vertex (finRotate C.length i))) =
      (∑ i : Fin C.length, phase (C.vertex i)) + (C.length : ZMod T) := by
    simp_rw [h _ _ (C.arc _)]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one]
  rw [Equiv.sum_comp (finRotate C.length) (fun i => phase (C.vertex i))] at hs
  have hz : (C.length : ZMod T) = 0 := by
    exact add_left_cancel (hs.symm.trans (add_zero _).symm)
  exact (ZMod.natCast_eq_zero_iff C.length T).mp hz

/-- Every nonempty cyclic-layer cycle completes at least one full round. -/
theorem layer_cycle_length {G : Type*} [Group G] {T : ℕ} (S : ZMod T → Set G)
    (C : Cycle (CyclicLayerDigraph S)) : T ≤ C.length := by
  exact Nat.le_of_dvd (lt_of_lt_of_le (by decide : 0 < 2) C.two_le)
    (C.phase_length_dvd T Prod.snd (fun _ _ h => h.1))

/-- At least two layers avoid the exceptional one-vertex loop convention. -/
theorem stronglyConnected_layer_cycle {G : Type*} [Group G] {T : ℕ} (hT : 2 ≤ T)
    (S : ZMod T → Set G) (h : StronglyConnected (CyclicLayerDigraph S)) :
    ∃ C : Cycle (CyclicLayerDigraph S), T ≤ C.length := by
  have hone : (1 : ZMod T) ≠ 0 := by
    intro he
    have hd : T ∣ 1 := (ZMod.natCast_eq_zero_iff 1 T).mp (by simpa only [Nat.cast_one] using he)
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  let : Nontrivial (ZMod T) := ⟨⟨1,0,hone⟩⟩
  obtain ⟨C⟩ := stronglyConnected_cycle h
  exact ⟨C,layer_cycle_length S C⟩

end DirectedCycles
