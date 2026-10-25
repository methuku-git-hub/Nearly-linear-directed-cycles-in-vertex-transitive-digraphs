module

public import DirectedCycles.ExpansionSegments

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The first half-open vertex is the prescribed start of a nonempty word. -/
theorem wordTails_head {G : Type*} [Group G] (x : G) (xs : List G) (hne : xs ≠ []) :
    (wordTails x xs).head? = some x := by cases xs with
  | nil => exact (hne rfl).elim
  | cons a xs => rfl

/-- The final half-open vertex has the word's closing edge to its endpoint. -/
theorem wordTails_last_arc {G : Type*} [Group G] (S : Set G) (x : G) (xs : List G)
    (hs : ∀ a ∈ xs, a ∈ S) :
    ∀ y ∈ (wordTails x xs).getLast?, CayleyDigraph S y (x*xs.prod) := by
  have hc := wordVertices_chain S x xs hs
  rw [wordVertices_eq_tails_append] at hc
  intro y hy
  exact (List.isChain_append.mp hc).2.2 y hy (x*xs.prod) (by simp)

namespace ExpansionTemplate
variable {G I : Type*} [Group G] {a : G} {l : I → ℕ} {D : ℕ}

/-- The explicit expansion yields a simple cycle once its quotient
coordinates are identified. Its length is the exact sum of expanded edge
lengths, hence never less than the auxiliary cycle length. -/
theorem simple_cycle {Q : Type*} [Group Q] (E : ExpansionTemplate G I a l D)
    (q : G →* Q) (h : ℕ) (hgap : ∀ i, l i+2*D+2 ≤ h)
    (hpow : (q a)^h = 1) (r : I → Q)
    (hcoord : Function.Injective (fun z : I × Fin h => r z.1*(q a)^z.2.val))
    (hx : ∀ e, q (E.vertex e) = r (E.position e)*(q a)^(E.level e))
    (S : Set G) (ha : a ∈ S) (hs : ∀ e, E.label e ∈ S) :
    ∃ C : Cycle (CayleyDigraph S), C.length = ∑ e, E.pointCount e ∧ E.length ≤ C.length ∧
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
      exact (wordVertices_chain S (E.vertex e) (E.edgeWord e) (E.edgeWord_allowed S ha hs e)).dropLast) (by
      intro e x hx' y hy'
      rw [E.points_eq_wordTails] at hx'
      rw [E.points_eq_wordTails,wordTails_head _ _ (E.edgeWord_nonempty _)] at hy'
      have hy : y = E.vertex (finRotate E.length e) := by
        simpa only [Option.mem_some_iff,eq_comm] using hy'
      subst y
      rw [← E.edgeWord_end e]
      exact wordTails_last_arc S (E.vertex e) (E.edgeWord e) (E.edgeWord_allowed S ha hs e) x hx')
  refine ⟨C,?_,hL,hV⟩
  simpa only [List.length_ofFn] using hC

end ExpansionTemplate
end DirectedCycles
