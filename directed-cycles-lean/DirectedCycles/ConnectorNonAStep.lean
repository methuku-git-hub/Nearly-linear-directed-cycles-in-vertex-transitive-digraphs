import DirectedCycles.ExpansionSegments

set_option autoImplicit false
namespace DirectedCycles

/-- In a connector word, the only possible non-a step has prefix a^j. -/
theorem connector_non_a_step {G : Type*} [Group G] (a s : G) (j m : ℕ)
    (k : ℕ) (hk : k < (List.replicate j a ++ [s] ++ List.replicate m a).length)
    (hne : (List.replicate j a ++ [s] ++ List.replicate m a)[k] ≠ a) :
    k = j ∧ ((List.replicate j a ++ [s] ++ List.replicate m a).take k).prod = a^j := by
  have hkj : k = j := by
    by_cases hl : k < j+1
    · rw [List.getElem_append_left (by simpa only [List.length_append,List.length_replicate,List.length_singleton] using hl)] at hne
      by_cases hlj : k < j
      · rw [List.getElem_append_left (by simpa only [List.length_replicate] using hlj),List.getElem_replicate] at hne
        exact (hne rfl).elim
      · omega
    · rw [List.getElem_append_right (by simp only [List.length_append,List.length_replicate,List.length_singleton]; omega),
        List.getElem_replicate] at hne
      exact (hne rfl).elim
  refine ⟨hkj,?_⟩
  rw [hkj,List.take_append_of_le_length (by simp)]
  rw [List.take_append_of_le_length (by simp),List.take_replicate,Nat.min_self,List.prod_replicate]

namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- Any non-a step in a template word is the connector's s-edge. -/
theorem edgeWord_non_a_step (E : ExpansionTemplate G I a l D) (e : Fin E.length)
    (i : Fin (E.edgeWord e).length) (h : (E.edgeWord e)[i.val] ≠ a) :
    E.level e = l (E.position e) ∧
      ((E.edgeWord e).take i.val).prod = a^(E.choice e).val := by
  by_cases he : E.level e < l (E.position e)
  · have hw : E.edgeWord e = [a] := by simp only [edgeWord,he,ite_true]
    have hi : i.val = 0 := by have := i.isLt; simp only [hw,List.length_singleton] at this; omega
    simp only [hw,hi,List.getElem_cons_zero,ne_eq,not_true_eq_false] at h
  · have hlev : E.level e = l (E.position e) := le_antisymm (E.level_le e) (by omega)
    have hw : E.edgeWord e = List.replicate (E.choice e).val a ++ [E.label e] ++
        List.replicate (D-(E.choice e).val) a := by simp only [edgeWord,he,ite_false]
    have hi : i.val < (List.replicate (E.choice e).val a ++ [E.label e] ++
        List.replicate (D-(E.choice e).val) a).length := by simpa only [← hw] using i.isLt
    have hh : (List.replicate (E.choice e).val a ++ [E.label e] ++
        List.replicate (D-(E.choice e).val) a)[i.val] ≠ a := by simpa only [← hw] using h
    have hp := (connector_non_a_step a (E.label e) (E.choice e).val (D-(E.choice e).val) i.val hi hh).2
    exact ⟨hlev,by simpa only [← hw] using hp⟩

end ExpansionTemplate
end DirectedCycles
