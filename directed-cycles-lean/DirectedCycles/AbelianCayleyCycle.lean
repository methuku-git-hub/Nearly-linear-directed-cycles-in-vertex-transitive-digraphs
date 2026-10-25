module

public import DirectedCycles.AbelianHamiltonianPath
public import DirectedCycles.MinimalGenerators
public import DirectedCycles.CosetPathCycle
public import DirectedCycles.CyclicCosetSpanning
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The abelian Cayley case of Lemma 6.2, including the stronger assertion
that deleting the final cycle vertex preserves spanning under the prime cutoff. -/
theorem abelian_cayley_cycle {G : Type*} [CommGroup G] [Finite G] [Nontrivial G]
    (S : Set G) (hgen : Subgroup.closure S = ⊤) :
    ∃ C : Cycle (CayleyDigraph S), (Nat.card G : ℝ)/2+1 ≤ C.length ∧
      ∀ D : ℕ, (∀ p : ℕ, p.Prime → p ∣ Nat.card G → 8*D+4 < p) →
        SpansTruncation D {x | x ∈ (List.ofFn C.vertex).dropLast} := by
  classical
  obtain ⟨a,T,ha,hT,hH,hgenT⟩ := minimal_generator_removal S hgen
  let H := Subgroup.closure (T : Set G)
  have hfull : H ⊔ Subgroup.zpowers a = ⊤ := by
    simpa only [H,Set.insert_eq,Subgroup.closure_union,← Subgroup.zpowers_eq_closure,sup_comm] using hgenT
  have hquot := quotient_generated_by_remaining_label H a hfull
  have hqa : QuotientGroup.mk' H a ≠ 1 := by
    intro he
    have haH : a ∈ H := (QuotientGroup.eq_one_iff _).mp he
    have hle : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.mpr haH
    have htop : H = ⊤ := by simpa only [sup_eq_left.mpr hle] using hfull
    exact hH htop
  have hm : 2 ≤ orderOf (QuotientGroup.mk' H a) := by
    have hp := (isOfFinOrder_of_finite (QuotientGroup.mk' H a)).orderOf_pos
    have hn : orderOf (QuotientGroup.mk' H a) ≠ 1 := fun h => hqa (orderOf_eq_one_iff.mp h)
    omega
  obtain ⟨P,hnd,hh,hc,hmem⟩ := abelian_generated_hamiltonian_path T
  have hc' : P.IsChain (CayleyDigraph S) := hc.imp (fun _ _ ⟨s,hs,he⟩ => ⟨s,hT hs,he⟩)
  obtain ⟨C,y,hy,hlen,hcosets⟩ := cycle_from_cyclic_quotient H S a ha hm P hnd hh hc' hmem
  let m := orderOf (QuotientGroup.mk' H a)
  have hcard : m*Nat.card H = Nat.card G := by
    rw [show m = Nat.card (G ⧸ H) from orderOf_eq_card_of_zpowers_eq_top hquot]
    exact H.index_mul_card
  refine ⟨C,?_,?_⟩
  · have hlen' : ((m-1 : ℕ) : ℝ)*Nat.card H+1 ≤ C.length := by exact_mod_cast hlen
    have hcard' : (m : ℝ)*Nat.card H = Nat.card G := by exact_mod_cast hcard
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hHpos : (0 : ℝ) < Nat.card H := by exact_mod_cast (Nat.card_pos (α := H))
    rw [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one] at hlen'
    nlinarith
  · intro D hprime
    have hm0 : m ≠ 1 := by omega
    have hmp : m.minFac.Prime := Nat.minFac_prime hm0
    have hdvd : m.minFac ∣ Nat.card G := (Nat.minFac_dvd m).trans ⟨Nat.card H,hcard.symm⟩
    have hpbound := hprime m.minFac hmp hdvd
    have hp_le : m.minFac ≤ m := Nat.minFac_le (by omega)
    have hD : D ≤ m-1 := by omega
    apply cyclic_quotient_full_cosets_span H D y (by rwa [hy])
    intro i hi u
    exact hcosets i (lt_of_lt_of_le hi hD) u

end DirectedCycles
