import DirectedCycles.TemplateCycle

set_option autoImplicit false
namespace DirectedCycles
namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- The expanded cycle also preserves any stronger relation satisfied along
all chosen word paths; this lets successor constraints survive concatenation. -/
theorem cycle_of_word_chains {Q : Type*} [Group Q] (E : ExpansionTemplate G I a l D)
    (q : G →* Q) (h : ℕ) (hgap : ∀ i, l i+2*D+2 ≤ h)
    (hpow : (q a)^h = 1) (r : I → Q)
    (hcoord : Function.Injective (fun z : I × Fin h => r z.1*(q a)^z.2.val))
    (hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e))
    (R : Digraph G) (hchain : ∀ e, (wordVertices (E.vertex e) (E.edgeWord e)).IsChain R) :
    ∃ C : Cycle R, C.length = ∑ e, E.pointCount e ∧ E.length ≤ C.length ∧
      List.ofFn C.vertex = (List.ofFn (fun e => List.ofFn (E.point e))).flatten := by
  have hinj := E.points_injective q h hgap hpow r hcoord hx
  have hlocal : ∀ e, Function.Injective (E.point e) := by
    intro e i j hij
    have he : (⟨e,i⟩ : (e : Fin E.length) × Fin (E.pointCount e)) = ⟨e,j⟩ := hinj hij
    exact (Sigma.mk.inj_iff.mp he).2 |> eq_of_heq
  have hne : ∀ e, List.ofFn (E.point e) ≠ [] := by
    intro e he
    have hl := congrArg List.length he
    simp only [List.length_ofFn,List.length_nil] at hl
    have := E.pointCount_pos e
    omega
  obtain ⟨C,hC,hL,hV⟩ := cycle_of_disjoint_segments E.two_le
    (fun e => List.ofFn (E.point e)) hne
    (fun e => List.nodup_ofFn.mpr (hlocal e)) (by
      intro e f hef
      apply List.disjoint_left.mpr
      intro v hv hv'
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hv'
      have he : (⟨e,i⟩ : (e : Fin E.length) × Fin (E.pointCount e)) = ⟨f,j⟩ := hinj hj.symm
      exact hef (congrArg Sigma.fst he)) (by
      intro e
      rw [E.points_eq_wordTails,← wordVertices_dropLast]
      exact (hchain e).dropLast) (by
      intro e x hx' y hy'
      rw [E.points_eq_wordTails] at hx'
      rw [E.points_eq_wordTails,wordTails_head _ _ (E.edgeWord_nonempty _)] at hy'
      have hy : y = E.vertex (finRotate E.length e) := by
        simpa only [Option.mem_some_iff,eq_comm] using hy'
      subst y
      rw [← E.edgeWord_end e]
      have hc := hchain e
      rw [wordVertices_eq_tails_append] at hc
      exact (List.isChain_append.mp hc).2.2 x hx' _ (by simp))
  exact ⟨C,by simpa only [List.length_ofFn] using hC,hL,hV⟩

/-- Exact flattened vertex membership is the expected union of word points. -/
theorem expanded_vertex_mem {R : Digraph G} (E : ExpansionTemplate G I a l D)
    (C : Cycle R)
    (hV : List.ofFn C.vertex = (List.ofFn (fun e => List.ofFn (E.point e))).flatten)
    (i : Fin C.length) : ∃ e k, E.point e k = C.vertex i := by
  have hv : C.vertex i ∈ List.ofFn C.vertex := List.mem_ofFn.mpr ⟨i,rfl⟩
  rw [hV] at hv
  obtain ⟨xs,hxs,hv⟩ := List.mem_flatten.mp hv
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hxs
  obtain ⟨k,hk⟩ := List.mem_ofFn.mp hv
  exact ⟨e,k,hk⟩

end ExpansionTemplate
end DirectedCycles
