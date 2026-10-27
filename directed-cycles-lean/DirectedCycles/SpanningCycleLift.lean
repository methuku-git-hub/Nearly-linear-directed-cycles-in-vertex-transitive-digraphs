module

public import DirectedCycles.SpanningAuxiliaryCycle
public import DirectedCycles.LayerCycleExpansion
public import DirectedCycles.LiftCardinalities

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The large-prime lift, using the actual auxiliary group and retaining
the additive spanning invariant. Its loss is linear in the quotient length. -/
theorem spanning_cycle_lift {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (a : G) (S : Set G) (ha : a ∈ S) (n : ℕ) (hn : Group.nilpotencyClass G ≤ n)
    (hh : 8*(n+1)+4 < Nat.card (elementClosure a ⧸
      (elementCommutators a).subgroupOf (elementClosure a)))
    (Q : Cycle (CayleyDigraph ((QuotientGroup.mk' (elementClosure a)) '' S)))
    (hQ : SpansTruncation (n+1) (Set.range Q.vertex))
    (b eta : ℝ) (hb : 0 ≤ b)
    (hlayer : LayerSpanningBound (elementCommutators a) (n+1) b eta)
    (hp : AbovePrimeCutoff G (n+1)) :
    ∃ C : Cycle (CayleyDigraph S),
      b/4*(Q.length : ℝ)*Nat.card (elementClosure a)*
        (Nat.card (elementCommutators a) : ℝ)^(-eta) ≤ C.length ∧
      C.ClosedUnderGenerator a ∧ SpansTruncation (n+1) (C.generatorTails a) := by
  obtain ⟨input,hlen,hspan⟩ := exists_chosen_lift_input_spanning a S (n+1) hh Q
  have hprefix := hspan hQ
  have hpB := hp.of_card_dvd (elementCommutators a).card_subgroup_dvd_card
  obtain ⟨QA,hQA,hQAspan⟩ := chosen_auxiliary_spanning_cycle a S n hn input hprefix
    b eta hlayer hpB
  obtain ⟨C,hC,hA,hCspan⟩ := expanding_layer_cycle a (n+1) input.data input.nonempty
    input.nu input.endpoint input.congruence input.prefixes input.bounds S ha input.labels QA
  refine ⟨C,?_,hA,hCspan hprefix hQAspan⟩
  let B := elementCommutators a
  let K := elementClosure a
  let h := Nat.card (K ⧸ B.subgroupOf K)
  let T := (slotBaseline (cyclicLiftSlots a (n+1) input.data)).length
  have hBpos : (0 : ℝ) < Nat.card B := by exact_mod_cast (Nat.card_pos (α := B))
  have hKB : (Nat.card K : ℝ) = (h : ℝ)*Nat.card B := by
    have he := (B.subgroupOf K).index_mul_card
    rw [Subgroup.index_eq_card,Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show B ≤ K from le_sup_right)).toEquiv] at he
    exact_mod_cast he.symm
  have hT : (Q.length : ℝ)*h/4 ≤ T := by
    have ht := input.quarter_bound.le
    simpa only [slotBaseline_length,cyclicLiftSlots_length,hlen,T,h,B,K] using ht
  have hscale := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hb)
    (Real.rpow_nonneg hBpos.le (1-eta))
  have hfinal : b*((Q.length : ℝ)*h/4)*(Nat.card B : ℝ)^(1-eta) ≤ C.length :=
    hscale.trans (hQA.trans (by exact_mod_cast hC))
  have hrpow : (Nat.card B : ℝ)^(1-eta) = (Nat.card B : ℝ)*(Nat.card B : ℝ)^(-eta) := by
    rw [sub_eq_add_neg,Real.rpow_add hBpos,Real.rpow_one]
  change b/4*(Q.length : ℝ)*Nat.card K*(Nat.card B : ℝ)^(-eta) ≤ C.length
  rw [hKB]
  rw [hrpow] at hfinal
  nlinarith only [hfinal]

/-- Passing to the vertex set loses none of the tail-spanning conclusion. -/
theorem Cycle.spans_of_generatorTails {G : Type*} [Group G] {R : Digraph G}
    (C : Cycle R) (a : G) (D : ℕ) (h : SpansTruncation D (C.generatorTails a)) :
    SpansTruncation D (Set.range C.vertex) := by
  apply h.mono
  rintro x ⟨i,rfl,_⟩
  exact ⟨i,rfl⟩

end DirectedCycles
