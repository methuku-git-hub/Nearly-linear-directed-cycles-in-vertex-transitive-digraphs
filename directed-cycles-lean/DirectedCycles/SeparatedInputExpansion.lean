import DirectedCycles.SeparatedInputCoordinates

set_option autoImplicit false
namespace DirectedCycles
namespace SeparatedLiftInput
variable {G J : Type*} [Group G] [Finite G] {a : G}
  {S : Set (G ⧸ elementClosure a)} {C : Cycle (CayleyDigraph S)}
  {s : Fin C.length → G}
  {hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*QuotientGroup.mk' (elementClosure a) (s i)}
  {t : J → G} {D : ℕ}

/-- Every auxiliary cycle expands with the exact source and target
residue coordinates selected for the return-path separation proof. -/
theorem expanded_cycle_coordinates (X : SeparatedLiftInput a S C s hstep t D)
    (T : Set G) (hs : ∀ i, s i ∈ T)
    (hh : 2*D+2 ≤ orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (Q : Cycle (cyclicAuxiliaryGraph a D X.data X.data_nonempty)) :
    ∃ L : Cycle (CayleyDigraph (insert a T)), Q.length ≤ L.length ∧ L.ClosedUnderGenerator a ∧
      ∀ e, L.vertex (finRotate L.length e) = L.vertex e*a ∨
        ∃ i : Fin C.length, ∃ u : ℕ, u ≤ D ∧
          L.vertex (finRotate L.length e) = L.vertex e*s i ∧
          QuotientGroup.mk' (elementCommutators a) (L.vertex e) =
            residuePower (QuotientGroup.mk' (elementCommutators a) a) (X.residues i+u)*
              QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take i.val).prod ∧
          QuotientGroup.mk' (elementCommutators a) (L.vertex (finRotate L.length e)) =
            residuePower (QuotientGroup.mk' (elementCommutators a) a) (X.residues i+u)*
              QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take (i.val+1)).prod := by
  have hgap : ∀ p : Fin X.data.length, (X.data[p.val]).1+2*D+2 ≤
      orderOf (QuotientGroup.mk' (elementCommutators a) a) := by
    intro p
    have hp : p.val < C.length := by simpa only [X.data_length] using p.isLt
    rw [X.data_get p]
    have hb := (X.bounds ⟨p.val,hp⟩).2.2
    omega
  have hlabels : ∀ p : Fin X.data.length, (X.data[p.val]).2 ∈ insert a T := by
    intro p
    rw [X.data_get p]
    exact Set.mem_insert_of_mem a (hs _)
  obtain ⟨L,hL,hclosed,hdata⟩ := cyclic_auxiliary_cycle_expands_with_edge_data a D X.data X.data_nonempty
    X.group_le X.data_prefixes hgap (insert a T) (Set.mem_insert a T) hlabels Q
  refine ⟨L,hL,hclosed,?_⟩
  intro e
  rcases hdata e with he | ⟨p,u,hu,he,hx⟩
  · exact Or.inl he
  · have hp : p.val < C.length := by simpa only [X.data_length] using p.isLt
    let i : Fin C.length := ⟨p.val,hp⟩
    have hli : (X.data[p.val]).1 = X.runs i := congrArg Prod.fst (X.data_get p)
    have hsi : (X.data[p.val]).2 = s i := congrArg Prod.snd (X.data_get p)
    rw [hsi] at he
    rw [hli] at hx
    have hsource := hx.trans (X.source_residue i u)
    refine Or.inr ⟨i,u,hu,he,hsource,?_⟩
    rw [he,map_mul,hsource,mul_assoc,← map_mul,← ofFn_prefix_product_succ s i]

end SeparatedLiftInput
end DirectedCycles
