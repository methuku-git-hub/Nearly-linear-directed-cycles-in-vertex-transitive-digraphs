import DirectedCycles.SingleRoundProducts
import DirectedCycles.TemplateEdgeCondition

set_option autoImplicit false
namespace DirectedCycles

/-- Every Cayley-cycle edge over the one-change round products has an actual
allowed representing round. Distinguished baseline edges use the baseline. -/
theorem choose_cycle_round_words {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (xs : List G) (hxs : LayerWord S 0 xs)
    (C : Cycle (CayleyDigraph (singleRoundProducts S xs))) :
    ∃ w : Fin C.length → List G, ∀ i,
      SingleChangeWord xs (w i) ∧ LayerWord S 0 (w i) ∧
      C.vertex (finRotate C.length i) = C.vertex i*(w i).prod ∧
      (C.vertex (finRotate C.length i) = C.vertex i*xs.prod → w i = xs) := by
  classical
  have hw : ∀ i, ∃ ys : List G, SingleChangeWord xs ys ∧ LayerWord S 0 ys ∧
      C.vertex (finRotate C.length i) = C.vertex i*ys.prod ∧
      (C.vertex (finRotate C.length i) = C.vertex i*xs.prod → ys = xs) := by
    intro i
    by_cases hi : C.vertex (finRotate C.length i) = C.vertex i*xs.prod
    · exact ⟨xs,Or.inl rfl,hxs,hi,fun _ => rfl⟩
    · obtain ⟨a,⟨ys,hchange,hallowed,he⟩,hnext⟩ := C.arc i
      refine ⟨ys,hchange,hallowed,?_,fun h => (hi h).elim⟩
      rwa [he]
  choose w hw using hw
  exact ⟨w,hw⟩

/-- A point on a representing round has one of the two exact coordinate
forms in the manuscript: a translated start or a translated end. -/
theorem representing_round_prefix {G : Type*} [Group G] (xs ys : List G)
    (h : SingleChangeWord xs ys) (x z : G) (he : z = x*ys.prod)
    (k : ℕ) (hk : k ≤ xs.length) :
    x*(ys.take k).prod = x*(xs.take k).prod ∨
      x*(ys.take k).prod = z*xs.prod⁻¹*(xs.take k).prod := by
  rcases singleChangeWord_prefix xs ys h k hk with hb | ha
  · exact Or.inl (congrArg (x*·) hb)
  · right
    rw [ha,he]
    group

/-- The distinguished-edge condition eliminates the mixed intersection case. -/
theorem Cycle.mixed_round_indices_equal {G : Type*} [Group G] {S : Set G}
    (C : Cycle (CayleyDigraph S)) (t : G) (hC : C.ClosedUnderGenerator t)
    (i j : Fin C.length)
    (he : C.vertex (finRotate C.length j) = C.vertex i*t) : i = j := by
  have hi := hC i ⟨finRotate C.length j,he⟩
  exact (finRotate C.length).injective (C.vertex.injective (hi.trans he.symm))

end DirectedCycles
