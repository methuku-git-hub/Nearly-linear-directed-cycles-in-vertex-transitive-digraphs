import DirectedCycles.ExpansionProjection

set_option autoImplicit false
namespace DirectedCycles
namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- The chosen generator word of one auxiliary edge. -/
def edgeWord (E : ExpansionTemplate G I a l D) (e : Fin E.length) : List G :=
  if E.level e < l (E.position e) then [a]
  else List.replicate (E.choice e).val a ++ [E.label e] ++ List.replicate (D-(E.choice e).val) a

theorem edgeWord_length (E : ExpansionTemplate G I a l D) (e : Fin E.length) :
    (E.edgeWord e).length = E.pointCount e := by
  unfold edgeWord pointCount
  split_ifs
  · rfl
  · have := (E.choice e).isLt
    simp only [List.length_append,List.length_replicate,List.length_singleton]
    omega

theorem pointCount_pos (E : ExpansionTemplate G I a l D) (e : Fin E.length) :
    0 < E.pointCount e := by unfold pointCount; split_ifs <;> omega

theorem edgeWord_nonempty (E : ExpansionTemplate G I a l D) (e : Fin E.length) :
    E.edgeWord e ≠ [] := by
  intro he
  have h := E.edgeWord_length e
  rw [he,List.length_nil] at h
  have := E.pointCount_pos e
  omega

theorem edgeWord_end (E : ExpansionTemplate G I a l D) (e : Fin E.length) :
    E.vertex e*(E.edgeWord e).prod = E.vertex (finRotate E.length e) := by
  unfold edgeWord
  split_ifs with he
  · simpa only [List.prod_singleton] using (E.fixed_end e he).symm
  · have hlevel : E.level e = l (E.position e) := le_antisymm (E.level_le e) (by omega)
    simpa only [List.prod_append,List.prod_replicate,List.prod_singleton,mul_assoc] using
      (E.connector_end e hlevel).symm

/-- The explicit point formula is exactly the half-open directed word walk. -/
theorem points_eq_wordTails (E : ExpansionTemplate G I a l D) (e : Fin E.length) :
    List.ofFn (E.point e) = wordTails (E.vertex e) (E.edgeWord e) := by
  by_cases he : E.level e < l (E.position e)
  · have hp : E.pointCount e = 1 := by simp only [pointCount,he,ite_true]
    have hpnt : ∀ k, E.point e k = E.vertex e := fun k => by simp only [point,he,ite_true]
    simp only [hpnt,List.ofFn_const,hp,List.replicate_one,edgeWord,he,ite_true,wordTails]
  · have hc : (E.choice e).val ≤ D := by have := (E.choice e).isLt; omega
    have hp : E.pointCount e = D+1 := by simp only [pointCount,he,ite_false]
    have hlevel : E.level e = l (E.position e) := le_antisymm (E.level_le e) (by omega)
    simp only [edgeWord,he,ite_false]
    rw [wordTails_connector]
    apply List.ext_getElem
    · simp only [List.length_ofFn,List.length_append,hp]; omega
    · intro k hk1 hk2
      have hk : k < D+1 := by simpa only [List.length_ofFn,hp] using hk1
      rw [List.getElem_ofFn]
      by_cases hkj : k ≤ (E.choice e).val
      · rw [List.getElem_append_left (by simpa only [List.length_ofFn] using (show k < (E.choice e).val+1 by omega)),
          List.getElem_ofFn]
        simp only [point,he,hkj,ite_false,ite_true]
      · rw [List.getElem_append_right (by simpa only [List.length_ofFn] using (show (E.choice e).val+1 ≤ k by omega))]
        simp only [List.length_ofFn,List.getElem_ofFn]
        simp only [point,he,hkj,ite_false]
        rw [E.connector_end e hlevel]
        have hshift : k-((E.choice e).val+1) < D-(E.choice e).val := by omega
        have h := connector_incoming_coordinate (E.vertex e) a (E.label e) D (E.choice e).val
          (k-((E.choice e).val+1)) hshift
        have hd : D-(E.choice e).val-(k-((E.choice e).val+1)) = D+1-k := by omega
        rw [hd] at h
        exact h.symm

/-- Every symbol in the chosen word is an available generator. -/
theorem edgeWord_allowed (E : ExpansionTemplate G I a l D) (S : Set G)
    (ha : a ∈ S) (hs : ∀ e, E.label e ∈ S) (e : Fin E.length) :
    ∀ b ∈ E.edgeWord e, b ∈ S := by
  intro b hb
  unfold edgeWord at hb
  split_ifs at hb
  · have he : b = a := List.mem_singleton.mp hb
    simpa only [he] using ha
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact (List.mem_replicate.mp hb).2 ▸ ha
      · exact (List.mem_singleton.mp hb) ▸ hs e
    · exact (List.mem_replicate.mp hb).2 ▸ ha

end ExpansionTemplate
end DirectedCycles
