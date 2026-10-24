import DirectedCycles.TemplateRetainedTails
import DirectedCycles.RoundExpansionWords

set_option autoImplicit false
namespace DirectedCycles

def Cycle.layerCoordinates {G : Type*} [Group G] {T : ℕ} {S : ZMod T → Set G}
    (C : Cycle (CyclicLayerDigraph S)) (z : ZMod T) : Set G :=
  {x | (x,z) ∈ Set.range C.vertex}

/-- One-change round expansion preserves simplicity and retains all translated
baseline-edge tails in every layer. -/
theorem expand_cycle_into_rounds {G : Type*} [Group G] {T : ℕ} [NeZero T]
    (S : ZMod T → Set G) (xs : List G) (hlen : xs.length = T)
    (hxs : LayerWord S 0 xs) (C : Cycle (CayleyDigraph (singleRoundProducts S xs)))
    (hC : C.ClosedUnderGenerator xs.prod) :
    ∃ L : Cycle (CyclicLayerDigraph S), L.length = T*C.length ∧
      ∀ z : ZMod T, ∀ x ∈ C.generatorTails xs.prod,
        x*(xs.take z.val).prod ∈ L.layerCoordinates z := by
  classical
  obtain ⟨w,hw⟩ := choose_cycle_round_words S xs hxs C
  have hwlen : ∀ i, (w i).length = T := fun i => (hw i).1.length.trans hlen
  let point : Fin C.length → Fin T → G × ZMod T := fun i j =>
    (C.vertex i*((w i).take j.val).prod,(j.val : ZMod T))
  let P : Fin C.length → List (G × ZMod T) := fun i => List.ofFn (point i)
  have hpoint_layer : ∀ i j k l, point i j = point k l → j = l := by
    intro i j k l he
    apply Fin.ext
    have h := congrArg (fun x : G × ZMod T => x.2.val) he
    simpa only [point,ZMod.val_natCast_of_lt j.isLt,ZMod.val_natCast_of_lt l.isLt] using h
  have hpoint_index : ∀ i j k l, point i j = point k l → i = k := by
    intro i j k l he
    have hj := hpoint_layer i j k l he
    subst l
    have hg := congrArg Prod.fst he
    change C.vertex i*((w i).take j.val).prod = C.vertex k*((w k).take j.val).prod at hg
    have hji : j.val ≤ xs.length := by rw [hlen]; exact j.isLt.le
    rcases representing_round_prefix xs (w i) (hw i).1 (C.vertex i)
      (C.vertex (finRotate C.length i)) (hw i).2.2.1 j.val hji with hi | hi <;>
    rcases representing_round_prefix xs (w k) (hw k).1 (C.vertex k)
      (C.vertex (finRotate C.length k)) (hw k).2.2.1 j.val hji with hk | hk
    · rw [hi,hk] at hg
      exact C.vertex.injective (mul_right_cancel hg)
    · rw [hi,hk] at hg
      have he' : C.vertex (finRotate C.length k) = C.vertex i*xs.prod := by
        have heq := mul_right_cancel hg
        calc C.vertex (finRotate C.length k) =
              (C.vertex (finRotate C.length k)*xs.prod⁻¹)*xs.prod := by group
             _ = C.vertex i*xs.prod := by rw [← heq]
      exact C.mixed_round_indices_equal xs.prod hC i k he'
    · rw [hi,hk] at hg
      have he' : C.vertex (finRotate C.length i) = C.vertex k*xs.prod := by
        have heq := mul_right_cancel hg
        calc C.vertex (finRotate C.length i) =
              (C.vertex (finRotate C.length i)*xs.prod⁻¹)*xs.prod := by group
             _ = C.vertex k*xs.prod := by rw [heq]
      exact (C.mixed_round_indices_equal xs.prod hC k i he').symm
    · rw [hi,hk] at hg
      exact C.successor_injective (mul_right_cancel (mul_right_cancel hg))
  have hPne : ∀ i, P i ≠ [] := by
    intro i he
    have h := congrArg List.length he
    simp only [P,List.length_ofFn,List.length_nil] at h
    exact NeZero.ne T h
  have hPnd : ∀ i, (P i).Nodup := by
    intro i
    apply List.nodup_ofFn.mpr
    intro j k he
    exact hpoint_layer i j i k he
  have hPdis : ∀ i j, i ≠ j → (P i).Disjoint (P j) := by
    intro i j hij
    apply List.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨k,hk⟩ := List.mem_ofFn.mp hx
    obtain ⟨l,hl⟩ := List.mem_ofFn.mp hx'
    exact hij (hpoint_index i k j l (hk.trans hl.symm))
  have hstep : ∀ i k, k < T →
      CyclicLayerDigraph S (C.vertex i*((w i).take k).prod,(k : ZMod T))
        (C.vertex i*((w i).take (k+1)).prod,((k+1 : ℕ) : ZMod T)) := by
    intro i k hk
    have hkw : k < (w i).length := by rw [hwlen]; exact hk
    refine ⟨by simp only [Nat.cast_add,Nat.cast_one],(w i)[k],?_,?_⟩
    · simpa only [zero_add] using (layerWord_iff_get S 0 (w i)).mp (hw i).2.1 ⟨k,hkw⟩
    · rw [← List.take_concat_get' (w i) k hkw,List.prod_append,List.prod_singleton,mul_assoc]
  have hPc : ∀ i, (P i).IsChain (CyclicLayerDigraph S) := by
    intro i
    apply List.isChain_ofFn.mpr
    intro k hk
    exact hstep i k (by omega)
  have hPh : ∀ i, (P i).head? = some (C.vertex i,0) := by
    intro i
    rw [List.head?_eq_getElem?,show P i = List.ofFn (point i) from rfl,List.getElem?_ofFn]
    simp only [Nat.pos_of_ne_zero (NeZero.ne T),dite_true,point,List.take_zero,List.prod_nil,
      mul_one,Nat.cast_zero]
  have hPl : ∀ i, (P i).getLast? = some (point i ⟨T-1,by have := NeZero.pos T; omega⟩) := by
    intro i
    rw [List.getLast?_eq_getElem?,show P i = List.ofFn (point i) from rfl,List.length_ofFn,
      List.getElem?_ofFn]
    simp only [show T-1 < T by have := NeZero.pos T; omega,dite_true]
  have hjoin : ∀ i, ∀ x ∈ (P i).getLast?, ∀ y ∈ (P (finRotate C.length i)).head?,
      CyclicLayerDigraph S x y := by
    intro i x hx y hy
    have hx' : x = point i ⟨T-1,by have := NeZero.pos T; omega⟩ := by
      simpa only [hPl,Option.mem_some_iff,eq_comm] using hx
    have hy' : y = (C.vertex (finRotate C.length i),0) := by
      simpa only [hPh,Option.mem_some_iff,eq_comm] using hy
    rw [hx',hy']
    have ht : T-1+1 = T := by have := NeZero.pos T; omega
    have hs := hstep i (T-1) (by have := NeZero.pos T; omega)
    have htake : (w i).take T = w i := List.take_of_length_le (hwlen i).le
    rw [ht,htake,ZMod.natCast_self,← (hw i).2.2.1] at hs
    exact hs
  obtain ⟨L,hL,_,hword⟩ := cycle_of_disjoint_segments C.two_le P hPne hPnd hPdis hPc hjoin
  refine ⟨L,?_,?_⟩
  · simpa only [P,List.length_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,Nat.mul_comm] using hL
  · intro z x hx
    obtain ⟨i,rfl,hi⟩ := hx
    have hwi := (hw i).2.2.2 hi
    have hj : z.val < T := ZMod.val_lt z
    have hp : point i ⟨z.val,hj⟩ = (C.vertex i*(xs.take z.val).prod,z) := by
      simp only [point,hwi,ZMod.natCast_zmod_val]
    have hmem : (C.vertex i*(xs.take z.val).prod,z) ∈ List.ofFn L.vertex := by
      rw [hword]
      apply List.mem_flatten.mpr
      refine ⟨P i,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
      exact List.mem_ofFn.mpr ⟨⟨z.val,hj⟩,hp⟩
    exact List.mem_ofFn.mp hmem

end DirectedCycles
