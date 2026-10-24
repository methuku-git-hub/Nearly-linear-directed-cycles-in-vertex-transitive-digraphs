import DirectedCycles.SeparatedInputReturnLift
import DirectedCycles.NormalizedOrbitPath
import DirectedCycles.PrescribedReturnSpine
import DirectedCycles.AuxiliaryGroupIndex

set_option autoImplicit false
namespace DirectedCycles

/-- The actual construction promised for one quotient cycle by Lemma 7.2.
All geometric and numerical conclusions concern its defined auxiliary graph. -/
structure ReturnLiftConstruction {G V : Type*} [Group G] [Finite G]
    (X : Digraph V) (a : G) (S : Set G)
    (C : Cycle (CayleyDigraph (QuotientGroup.mk' (elementClosure a) '' S)))
    (r c n : ℕ) where
  labels : Fin C.length → G
  label_mem : ∀ i, labels i ∈ S
  step : ∀ i, C.vertex (finRotate C.length i) =
    C.vertex i*QuotientGroup.mk' (elementClosure a) (labels i)
  runs : Fin C.length → ℕ
  bounds : ∀ i, n+1 ≤ runs i ∧
    (orderOf (QuotientGroup.mk' (elementCommutators a) a)+7)/8 ≤ runs i ∧
    runs i ≤ orderOf (QuotientGroup.mk' (elementCommutators a) a)-2*(n+1)-2
  closing : ℤ
  endpoint : QuotientGroup.mk' (elementCommutators a) (List.ofFn labels).prod =
    (QuotientGroup.mk' (elementCommutators a) a)^closing
  congruence : (orderOf (QuotientGroup.mk' (elementCommutators a) a) : ℤ) ∣
    ((∑ i, (runs i+(n+1)) : ℕ) : ℤ)+closing
  nonempty : cycleRunData runs labels ≠ []
  connected : StronglyConnected (cyclicAuxiliaryGraph a (n+1) (cycleRunData runs labels) nonempty)
  group_le : cyclicAuxiliaryGroup a (n+1) (cycleRunData runs labels) nonempty ≤ elementCommutators a
  layers : C.length*orderOf (QuotientGroup.mk' (elementCommutators a) a) ≤
    8*(slotBaseline (cyclicLiftSlots a (n+1) (cycleRunData runs labels))).length
  index_bound :
    (((cyclicAuxiliaryGroup a (n+1) (cycleRunData runs labels) nonempty).subgroupOf
      (elementCommutators a)).index : ℝ) ≤
      auxiliaryIndexConstant r c n *
        ((Nat.card (G ⧸ elementClosure a) : ℝ)/C.length)^auxiliaryIndexExponent r c n
  lift : ∀ Q : Cycle (cyclicAuxiliaryGraph a (n+1) (cycleRunData runs labels) nonempty),
    ∃ L : Cycle X, Q.length ≤ L.length

/-- Lemma 7.2 in free-action coordinates, with all paths, run lengths,
collision constraints, and auxiliary-graph data constructed in the proof. -/
theorem based_return_lifting {G I : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    [Fintype I] [DecidableEq I]
    (V : I → I → Set G) (a : G) (W : OrbitCycleWalk (VoltageDigraph V) a)
    (hstart : (W.point 0).1 = 1) (hsc : StronglyConnected (VoltageDigraph V))
    (r c n : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c) (hn : c ≤ n)
    (hh : 8*(Fintype.card I+1)*((n+1)+1) < orderOf (QuotientGroup.mk' (elementCommutators a) a)) :
    ∃ S : Set G, (∀ s ∈ S, s ∉ elementClosure a) ∧
      StronglyConnected (CayleyDigraph (QuotientGroup.mk' (elementClosure a) '' S)) ∧
      ∀ C : Cycle (CayleyDigraph (QuotientGroup.mk' (elementClosure a) '' S)),
        Nonempty (ReturnLiftConstruction (VoltageDigraph V) a S C r c n) := by
  classical
  have ha : a ≠ 1 := by
    intro he
    simp only [he,map_one,orderOf_one] at hh
    nlinarith
  have hhsmall : 2*(n+1)+2 ≤ orderOf (QuotientGroup.mk' (elementCommutators a) a) := by
    nlinarith
  obtain ⟨p,_hp,R,ht,hpot,hsc'⟩ := W.exists_prescribed_return_spine hstart hsc
  let W' := W.changeRepresentatives p
  have hcoord : ∀ k : Fin W'.length, (W'.point k.castSucc).1 = 1 :=
    W.changeRepresentatives_internal p hpot
  let A := W'.normalizedRootPath ha hcoord
  let Q₀ := Set.range W.orbitIndex
  have htcycle : ∀ z ∈ Q₀, z ≠ (W.point 0).2 → R.voltage z = a := by
    rintro z ⟨k,rfl⟩ hz
    apply ht k
    by_contra he
    have hk : k = ⟨0,by have := W.two_le; omega⟩ := Fin.ext (by change k.val = 0; omega)
    exact hz (hk ▸ rfl)
  have hA : ∀ x z, z ∈ (A.translateRoot x).vertices.dropLast → z.1 = x ∧ z.2 ∈ Q₀ :=
    W'.normalizedRootPath_internal ha hcoord
  obtain ⟨S,hS,hSsc,P,hnd,hP⟩ := R.return_path_family (QuotientGroup.mk' (elementClosure a))
    (QuotientGroup.mk'_surjective (elementClosure a)) hsc'
  refine ⟨S,?_,hSsc,?_⟩
  · intro s hs hm
    exact hS s hs ((QuotientGroup.eq_one_iff s).mpr hm)
  · intro C
    obtain ⟨s,hs,hstep⟩ := cayley_cycle_labels (QuotientGroup.mk' (elementClosure a)) S C
    let J := {z : I // z ∉ Q₀}
    have hJ : Fintype.card J ≤ Fintype.card I := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    obtain ⟨X⟩ := exists_separated_lift_input a (QuotientGroup.mk' (elementClosure a) '' S)
      C s hstep (fun z : J => R.voltage z.val) (n+1) (Fintype.card I) hJ hh
    refine ⟨{
      labels := s
      label_mem := hs
      step := hstep
      runs := X.runs
      bounds := X.bounds
      closing := X.closing
      endpoint := X.endpoint
      congruence := X.congruence
      nonempty := X.data_nonempty
      connected := cyclicAuxiliaryGraph_stronglyConnected a (n+1) X.data X.data_nonempty
      group_le := X.group_le
      layers := ?_
      index_bound := ?_
      lift := ?_
    }⟩
    · rw [slotBaseline_length,cyclicLiftSlots_length,cycleRunData_sum]
      exact X.total
    · have hi := auxiliary_group_density_index a r c n hr hc hn X.data X.data_nonempty X.closing
        X.data_prefixes X.data_endpoint X.data_congruence
      rw [X.data_length] at hi
      exact hi
    · intro Q
      obtain ⟨L,hL⟩ := separated_input_return_lift (gaugeLabels V p) (W.point 0).2 a Q₀ R.voltage
        R.root_voltage htcycle (QuotientGroup.mk' (elementClosure a) '' S) C s hstep (n+1) X hhsmall
        A hA (fun i => P ⟨s i,hs i⟩) (fun i => hP ⟨s i,hs i⟩) (fun i => hnd ⟨s i,hs i⟩) Q
      exact ⟨L.map (gaugeCoordinates p).toEmbedding (fun x y h => (gaugeLabels_arc V p x y).mp h),hL⟩

end DirectedCycles
