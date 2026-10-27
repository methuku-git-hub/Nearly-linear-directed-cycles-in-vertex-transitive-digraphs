module

public import DirectedCycles.CyclePrefixEmbeddings
public import DirectedCycles.CycleRunResidueChoice
public import DirectedCycles.ReturnCollisionOffsets
public import DirectedCycles.ActualRunResidueCoordinates

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- All run and collision data selected for one fixed quotient cycle.
The source and target embeddings use the actual prefix products. -/
structure SeparatedLiftInput {G J : Type*} [Group G] [Finite G]
    (a : G) (S : Set (G ⧸ elementClosure a)) (C : Cycle (CayleyDigraph S))
    (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*QuotientGroup.mk' (elementClosure a) (s i))
    (t : J → G) (D : ℕ) where
  runs : Fin C.length → ℕ
  residues : Fin C.length → ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a))
  closing : ℤ
  endpoint : QuotientGroup.mk' (elementCommutators a) (List.ofFn s).prod =
    (QuotientGroup.mk' (elementCommutators a) a)^closing
  bounds : ∀ i, D ≤ runs i ∧ (orderOf (QuotientGroup.mk' (elementCommutators a) a)+7)/8 ≤ runs i ∧
    runs i ≤ orderOf (QuotientGroup.mk' (elementCommutators a) a)-2*D-2
  congruence : (orderOf (QuotientGroup.mk' (elementCommutators a) a) : ℤ) ∣
    ((∑ i, (runs i+D) : ℕ) : ℤ)+closing
  total : C.length*orderOf (QuotientGroup.mk' (elementCommutators a) a) ≤ 8*∑ i,(runs i+1)
  prefix_residues : ∀ i, (runPrefixSum runs D i.castSucc : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a)))+
    (runs i : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a))) = residues i
  run_residues : ∀ i, (runs i : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a))) =
    residues i-residues ((finRotate C.length).symm i)-(D : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a)))-
    (if i.val = 0 then (closing : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a))) else 0)
  offsets : RightCollision
    (cycleSourceEmbedding (QuotientGroup.mk' (elementClosure a)) S C s hstep)
    (cycleTargetEmbedding (QuotientGroup.mk' (elementClosure a)) S C s hstep)
    (fun j => QuotientGroup.mk' (elementClosure a) (t j)) →
    ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a))
  offset_eq : ∀ c,
    QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take c.val.2.1.val).prod *
      QuotientGroup.mk' (elementCommutators a) (t c.val.1) *
      (QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take (c.val.2.2.val+1)).prod)⁻¹ =
      residuePower (QuotientGroup.mk' (elementCommutators a) a) (offsets c)
  avoid : ∀ c, residues c.val.2.2-residues c.val.2.1 ∉
    collisionForbiddenResidues (orderOf (QuotientGroup.mk' (elementCommutators a) a)) D (offsets c)

theorem exists_separated_lift_input {G J : Type*} [Group G] [Finite G] [Fintype J]
    (a : G) (S : Set (G ⧸ elementClosure a)) (C : Cycle (CayleyDigraph S))
    (s : Fin C.length → G)
    (hstep : ∀ i, C.vertex (finRotate C.length i) = C.vertex i*QuotientGroup.mk' (elementClosure a) (s i))
    (t : J → G) (D q : ℕ) (hJ : Fintype.card J ≤ q)
    (hh : 8*(q+1)*(D+1) < orderOf (QuotientGroup.mk' (elementCommutators a) a)) :
    Nonempty (SeparatedLiftInput a S C s hstep t D) := by
  classical
  let b := QuotientGroup.mk' (elementCommutators a) a
  let h := orderOf b
  let : NeZero h := ⟨by dsimp only [h,b]; omega⟩
  let source := cycleSourceEmbedding (QuotientGroup.mk' (elementClosure a)) S C s hstep
  let target := cycleTargetEmbedding (QuotientGroup.mk' (elementClosure a)) S C s hstep
  let tag := fun j => QuotientGroup.mk' (elementClosure a) (t j)
  let K := RightCollision source target tag
  have he : ∀ c : K, ∃ e : ZMod h,
      QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take c.val.2.1.val).prod *
        QuotientGroup.mk' (elementCommutators a) (t c.val.1) *
        (QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take (c.val.2.2.val+1)).prod)⁻¹ =
        residuePower b e := by
    intro c
    exact element_collision_offset a _ _ _ c.property.1
  choose e he using he
  have hclose := cayley_cycle_word_closes (QuotientGroup.mk' (elementClosure a)) S C s hstep
  have hmem : (List.ofFn s).prod ∈ elementClosure a := (QuotientGroup.eq_one_iff _).mp hclose
  obtain ⟨ν,hν⟩ := elementClosure_quotient_power a (List.ofFn s).prod hmem
  obtain ⟨v,l,hb,hc,hT,hp,hr,havoid⟩ := choose_cycle_return_runs C.length h q D C.two_le hh hJ
    source target tag e ν
  exact ⟨⟨l,v,ν,hν,hb,hc,hT,hp,hr,e,he,havoid⟩⟩

end DirectedCycles
