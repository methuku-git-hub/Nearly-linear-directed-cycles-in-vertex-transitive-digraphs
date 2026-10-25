module

public import DirectedCycles.ResidueCollision

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem map_residuePower_eq_one {Q H : Type*} [Group Q] [Group H]
    (a : Q) (p : Q →* H) (ha : p a = 1) (z : ZMod (orderOf a)) :
    p (residuePower a z) = 1 := by simp only [residuePower,map_pow,ha,one_pow]

/-- At every quotient position, the incoming endpoint interval is
disjoint from the source interval and its a-translate. The closing
offset is incorporated in the finish representatives. -/
theorem connector_endpoints_separated {Q H I : Type*} [Group Q] [Group H]
    (a : Q) [NeZero (orderOf a)] (ha : a ∈ Subgroup.center Q)
    (p : Q →* H) (hpa : p a = 1) (σ : Equiv.Perm I)
    (start finish : I → Q) (hstart : Function.Injective (fun i => p (start i)))
    (v ν : I → ZMod (orderOf a)) (l : I → ℕ) (D : ℕ)
    (hfinish : ∀ i, finish (σ i) = residuePower a (ν i)*start i)
    (hl : ∀ i, (l i : ZMod (orderOf a)) = v i-v (σ i)-(D : ZMod (orderOf a))-ν i)
    (hb : ∀ i, 1 ≤ l i ∧ l i ≤ orderOf a-2*D-2) (hh : 2*D+2 ≤ orderOf a)
    (i j : I) (u u' ε : ℕ) (hu : u ≤ D) (hu' : u' ≤ D) (hε : ε ≤ 1) :
    residuePower a (v j+u')*finish j ≠ (residuePower a (v i+u)*start i)*a^ε := by
  intro he
  have hj : j = σ i := by
    have heq := congrArg p he
    simp only [map_mul,map_pow,hpa,one_pow,map_residuePower_eq_one a p hpa,one_mul,mul_one] at heq
    have hf := congrArg p (hfinish (σ.symm j))
    simp only [Equiv.apply_symm_apply,map_mul,map_residuePower_eq_one a p hpa,one_mul] at hf
    have hi := hstart (hf.symm.trans heq)
    exact (congrArg σ hi).symm.trans (σ.apply_symm_apply j) |>.symm
  subst j
  have hc := (residuePower_central a ha (ε : ZMod (orderOf a)) (start i)).eq
  rw [residuePower_natCast] at hc
  have hs : (residuePower a (v i+u)*start i)*a^ε =
      residuePower a (v i+(u+ε : ℕ))*start i := by
    rw [mul_assoc,← hc,← mul_assoc,← residuePower_natCast a ε,← residuePower_add]
    congr 2
    push_cast
    abel
  have hf : residuePower a (v (σ i)+u')*finish (σ i) =
      residuePower a (v i-(l i : ZMod (orderOf a))-(D : ZMod (orderOf a))+u')*start i := by
    rw [hfinish,← mul_assoc,← residuePower_add]
    congr 2
    rw [hl]
    abel
  rw [hs,hf] at he
  exact no_source_target_residue_collision a (start i) (v i) D (l i) (u+ε) u'
    (hb i).1 (hb i).2 hh (by omega) hu' he.symm

end DirectedCycles
