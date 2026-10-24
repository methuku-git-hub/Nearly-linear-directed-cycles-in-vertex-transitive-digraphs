import DirectedCycles.ListBlockEquiv
import DirectedCycles.ConnectorPositions

set_option autoImplicit false
namespace DirectedCycles

/-- A quotient position and one of its l_i+1 retained vertices. -/
abbrev RetainedPosition {G : Type*} (data : List (ℕ × G)) :=
  (i : Fin data.length) × Fin ((data[i.val]).1+1)

/-- The actual baseline-prefix position corresponding to (i,k). -/
def retainedPositionEquiv {G : Type*} [Group G] (a : G) (D : ℕ) (data : List (ℕ × G)) :
    RetainedPosition data ≃ Fin (cyclicBaselineWord a D data).length :=
  (listBlockEquiv data (fun z => z.1+1)).trans (finCongr (cyclicBaselineWord_length a D data).symm)

theorem retainedPositionEquiv_val {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) (k : Fin ((data[i.val]).1+1)) :
    (retainedPositionEquiv a D data ⟨i,k⟩).val =
      ((data.take i.val).map (fun z => z.1+1)).sum+k.val := by
  simp only [retainedPositionEquiv,Equiv.trans_apply,finCongr_apply,Fin.val_cast,listBlockEquiv_val]

/-- At every retained vertex, the actual baseline prefix consists of the
completed earlier blocks followed by the appropriate part of the fixed run. -/
theorem cyclicBaseline_take_retained {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) (k : Fin ((data[i.val]).1+1)) :
    (cyclicBaselineWord a D data).take (retainedPositionEquiv a D data ⟨i,k⟩).val =
      cyclicBaselineWord a D (data.take i.val) ++ List.replicate k.val a := by
  have hk : k.val ≤ (data[i.val]).1 := by have := k.isLt; omega
  have hf := flatBlock_take (fun z : ℕ × G => runConnectorBlock a D z.1 z.2)
    data i k.val (by simp only [runConnectorBlock_length]; omega)
  have hoff : flatBlockOffset (fun z : ℕ × G => runConnectorBlock a D z.1 z.2) data i =
      ((data.take i.val).map (fun z => z.1+1)).sum := cyclicBaselineWord_length a D (data.take i.val)
  rw [hoff] at hf
  have ht : (runConnectorBlock a D (data[i.val]).1 (data[i.val]).2).take k.val =
      List.replicate k.val a := by
    simp only [runConnectorBlock]
    rw [List.take_append_of_le_length (by simpa only [List.length_replicate] using hk)]
    simp only [List.take_replicate,Nat.min_eq_left hk]
  rw [ht] at hf
  rw [retainedPositionEquiv_val]
  exact hf

/-- The reference element at the start of the i-th fixed run. -/
def runReference {G : Type*} [Group G] (a : G) (D : ℕ) (data : List (ℕ × G))
    (i : Fin data.length) : G := (cyclicBaselineWord a D (data.take i.val)).prod

theorem cyclicBaseline_prefix_retained {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) (k : Fin ((data[i.val]).1+1)) :
    ((cyclicBaselineWord a D data).take (retainedPositionEquiv a D data ⟨i,k⟩).val).prod =
      runReference a D data i*a^k.val := by
  rw [cyclicBaseline_take_retained,List.prod_append,List.prod_replicate]
  rfl

/-- The quotient-position references retain the original distinct cosets. -/
theorem runReference_quotient {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (i : Fin data.length) :
    QuotientGroup.mk' (elementClosure a) (runReference a D data i) =
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc) := by
  rw [runReference,cyclicBaselineWord_mod_elementClosure]
  simp only [cycleLabelPrefixes,Fin.val_castSucc,List.map_take]

end DirectedCycles
