module

public import DirectedCycles.SeparatedInputCoordinates
public import DirectedCycles.ConnectorMixedSeparation

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The selected constraints rule out every mixed collision, including
the root and prescribed-cycle orbits, for distinct connectors. -/
theorem separated_return_mixed_collision {G I : Type*} [Group G] [Finite G]
    (a : G) (root : I) (Q₀ : Set I) (t : I → G) (htroot : t root = 1)
    (htcycle : ∀ z ∈ Q₀, z ≠ root → t z = a)
    (S : Set (G ⧸ elementClosure a)) (C : Cycle (CayleyDigraph S)) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*QuotientGroup.mk' (elementClosure a) (s i))
    (D : ℕ) (X : SeparatedLiftInput a S C s hstep (fun z : {z : I // z ∉ Q₀} => t z.val) D)
    (hh : 2*D+2 ≤ orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (i j : Fin C.length) (hij : i ≠ j) (u u' : ℕ) (hu : u ≤ D) (hu' : u' ≤ D)
    (x y : G)
    (hx : QuotientGroup.mk' (elementCommutators a) x =
      residuePower (QuotientGroup.mk' (elementCommutators a) a) (X.residues i+u)*
        QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take i.val).prod)
    (hy : QuotientGroup.mk' (elementCommutators a) y =
      residuePower (QuotientGroup.mk' (elementCommutators a) a) (X.residues j+u')*
        QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take (j.val+1)).prod) :
    ∀ z : I, y ≠ x*t z := by
  classical
  let q := QuotientGroup.mk' (elementCommutators a)
  let b := q a
  let : NeZero (orderOf b) := ⟨(orderOf_pos b).ne'⟩
  let p := QuotientGroup.map (elementCommutators a) (elementClosure a) (MonoidHom.id G)
    (by simpa only [Subgroup.comap_id] using (show elementCommutators a ≤ elementClosure a from le_sup_right))
  have hpb : p b = 1 := (QuotientGroup.eq_one_iff a).mpr (mem_elementClosure a)
  let start := fun k : Fin C.length => q ((List.ofFn s).take k.val).prod
  let finish := fun k : Fin C.length => q ((List.ofFn s).take (k.val+1)).prod
  have hstart : Function.Injective (fun k => p (start k)) :=
    (cycleSourceEmbedding (QuotientGroup.mk' (elementClosure a)) S C s hstep).injective
  have hfinish : Function.Injective (fun k => p (finish k)) :=
    (cycleTargetEmbedding (QuotientGroup.mk' (elementClosure a)) S C s hstep).injective
  have hb : ∀ k, 1 ≤ X.runs k ∧ X.runs k ≤ orderOf b-2*D-2 := by
    intro k
    have hk := X.bounds k
    have hn : 0 < orderOf b := orderOf_pos b
    change D ≤ X.runs k ∧ (orderOf b+7)/8 ≤ X.runs k ∧ X.runs k ≤ orderOf b-2*D-2 at hk
    exact ⟨by omega,hk.2.2⟩
  intro z he
  have heq := congrArg q he
  rw [map_mul,hx,hy] at heq
  by_cases hz : z = root
  · rw [hz,htroot,map_one,mul_one] at heq
    apply connector_endpoints_separated b (element_mod_commutators_central a) p hpb
      (finRotate C.length).symm start finish hstart X.residues
      (fun k => if k.val=0 then (X.closing : ZMod (orderOf b)) else 0) X.runs D
      X.finish_offsets X.run_residues hb hh i j u u' 0 hu hu' (by omega)
    simpa only [pow_zero,mul_one] using heq
  · by_cases hQ : z ∈ Q₀
    · rw [htcycle z hQ hz] at heq
      apply connector_endpoints_separated b (element_mod_commutators_central a) p hpb
        (finRotate C.length).symm start finish hstart X.residues
        (fun k => if k.val=0 then (X.closing : ZMod (orderOf b)) else 0) X.runs D
        X.finish_offsets X.run_residues hb hh i j u u' 1 hu hu' (by omega)
      simpa only [pow_one] using heq
    · exact connector_mixed_separated b p hpb start finish hstart hfinish
        (fun z : {z : I // z ∉ Q₀} => q (t z.val)) X.offsets X.offset_eq D X.residues X.avoid
        i j hij ⟨z,hQ⟩ u u' hu hu' heq

end DirectedCycles
