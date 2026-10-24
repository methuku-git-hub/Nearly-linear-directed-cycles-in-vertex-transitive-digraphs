import DirectedCycles.SeparatedInputExpansion
import DirectedCycles.SeparatedReturnCollisions
import DirectedCycles.ReturnEdgePaths

set_option autoImplicit false
namespace DirectedCycles

/-- Every actual auxiliary cycle lifts through the selected return paths.
All non-a path disjointness is discharged from the constructed residues,
quotient simplicity, and the prescribed-cycle return voltages. -/
theorem separated_input_return_lift {G I : Type*} [Group G] [Finite G]
    (V : I → I → Set G) (root : I) (a : G) (Q₀ : Set I) (t : I → G)
    (htroot : t root = 1) (htcycle : ∀ z ∈ Q₀, z ≠ root → t z = a)
    (S : Set (G ⧸ elementClosure a)) (C : Cycle (CayleyDigraph S)) (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*QuotientGroup.mk' (elementClosure a) (s i))
    (D : ℕ) (X : SeparatedLiftInput a S C s hstep (fun z : {z : I // z ∉ Q₀} => t z.val) D)
    (hh : 2*D+2 ≤ orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (A : SimplePath (VoltageDigraph V) (1,root) (a,root))
    (hA : ∀ x z, z ∈ (A.translateRoot x).vertices.dropLast → z.1 = x ∧ z.2 ∈ Q₀)
    (P : ∀ k, SimplePath (VoltageDigraph V) (1,root) (s k,root))
    (hP : ∀ k z, z ∈ (P k).vertices → z.1 = 1 ∨ z.1 = s k*(t z.2)⁻¹)
    (hnd : ∀ k, ((P k).vertices.map (fun z => (QuotientGroup.mk' (elementClosure a) z.1,z.2))).Nodup)
    (Q : Cycle (cyclicAuxiliaryGraph a D X.data X.data_nonempty)) :
    ∃ L : Cycle (VoltageDigraph V), Q.length ≤ L.length := by
  classical
  let q := QuotientGroup.mk' (elementCommutators a)
  let b := q a
  let p := QuotientGroup.map (elementCommutators a) (elementClosure a) (MonoidHom.id G)
    (by simpa only [Subgroup.comap_id] using (show elementCommutators a ≤ elementClosure a from le_sup_right))
  have hpq : ∀ g : G, p (q g) = QuotientGroup.mk' (elementClosure a) g := fun _ => rfl
  have hpb : p b = 1 := (QuotientGroup.eq_one_iff a).mpr (mem_elementClosure a)
  obtain ⟨L,hL,hclosed,hcoords⟩ := X.expanded_cycle_coordinates (Set.range s) (fun k => ⟨k,rfl⟩) hh Q
  have choices : ∀ e : Fin L.length, L.vertex (finRotate L.length e) ≠ L.vertex e*a →
      ∃ i : Fin C.length, ∃ u : ℕ, u ≤ D ∧
        L.vertex (finRotate L.length e) = L.vertex e*s i ∧
        q (L.vertex e) = residuePower b (X.residues i+u)*q ((List.ofFn s).take i.val).prod ∧
        q (L.vertex (finRotate L.length e)) = residuePower b (X.residues i+u)*q ((List.ofFn s).take (i.val+1)).prod := by
    intro e he
    exact (hcoords e).resolve_left he
  choose pos u hu hend hsource htarget using choices
  obtain ⟨M,hM⟩ := cycle_of_return_edge_paths V root a L hclosed t htroot Q₀ htcycle A hA s P hP
    pos hend (by
      intro i j hij hi hj
      have hxy : L.vertex i ≠ L.vertex j := fun he => hij (L.vertex.injective he)
      by_cases hp : pos i hi = pos j hj
      · have hqx : QuotientGroup.mk' (elementClosure a) (L.vertex i) =
            QuotientGroup.mk' (elementClosure a) ((List.ofFn s).take (pos i hi).val).prod := by
          have he := congrArg p (hsource i hi)
          simpa only [map_mul,map_residuePower_eq_one b p hpb,one_mul,hpq] using he
        have hqy : QuotientGroup.mk' (elementClosure a) (L.vertex j) =
            QuotientGroup.mk' (elementClosure a) ((List.ofFn s).take (pos j hj).val).prod := by
          have he := congrArg p (hsource j hj)
          simpa only [map_mul,map_residuePower_eq_one b p hpb,one_mul,hpq] using he
        have hqq : QuotientGroup.mk' (elementClosure a) (L.vertex i) =
            QuotientGroup.mk' (elementClosure a) (L.vertex j) := by rw [hqx,hqy,hp]
        rw [hp]
        exact (P (pos j hj)).translates_disjoint (QuotientGroup.mk' (elementClosure a)) (hnd _)
          (L.vertex i) (L.vertex j) hqq hxy
      · apply (P (pos i hi)).translates_disjoint_of_no_mixed (P (pos j hj)) t (hP _) (hP _)
          (L.vertex i) (L.vertex j) hxy
        · rw [← hend i hi,← hend j hj]
          exact fun he => hij ((finRotate L.length).injective (L.vertex.injective he))
        · intro z
          constructor
          · rw [← hend j hj]
            exact separated_return_mixed_collision a root Q₀ t htroot htcycle S C s hstep D X hh
              (pos i hi) (pos j hj) hp (u i hi) (u j hj) (hu i hi) (hu j hj)
              (L.vertex i) (L.vertex (finRotate L.length j)) (hsource i hi) (htarget j hj) z
          · rw [← hend i hi]
            exact separated_return_mixed_collision a root Q₀ t htroot htcycle S C s hstep D X hh
              (pos j hj) (pos i hi) (Ne.symm hp) (u j hj) (u i hi) (hu j hj) (hu i hi)
              (L.vertex j) (L.vertex (finRotate L.length i)) (hsource j hj) (htarget i hi) z)
  exact ⟨M,hL.trans hM⟩

end DirectedCycles
