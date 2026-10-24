import DirectedCycles.CycleContractionProjection
import DirectedCycles.BlockLift

set_option autoImplicit false
namespace DirectedCycles
namespace Cycle
variable {G I : Type*} [Group G] {D : Digraph (G × I)}

theorem contractProjection_fibres_strong (C : Cycle D)
    (hinj : Function.Injective (fun j => (C.vertex j).2))
    (hD : ∀ g : G, ∀ x y : G × I, D (g*x.1,x.2) (g*y.1,y.2) ↔ D x y) :
    ∀ w, StronglyConnected (fun x y : {v // C.contractProjection v = w} => D x.val y.val) := by
  rintro ⟨g,i⟩
  cases i with
  | none =>
    let e : G × I ≃ G × I := (Equiv.mulLeft g).prodCongr (Equiv.refl I)
    let L := C.map e.toEmbedding (fun x y h => (hD g x y).mpr h)
    apply cycle_fibre_stronglyConnected L C.contractProjection (g,none)
    · intro j
      exact C.contractProjection_cycle hinj g j
    · intro x hx
      obtain ⟨j,hj⟩ := (C.contractProjection_eq_none hinj x g).mp hx
      exact ⟨j,hj.symm⟩
  | some i =>
    intro x y
    have hx := (C.contractProjection_eq_some x.val g i).mp x.property
    have hy := (C.contractProjection_eq_some y.val g i).mp y.property
    have he : x = y := Subtype.ext (hx.trans hy.symm)
    subst y
    exact Relation.ReflTransGen.refl

/-- Simultaneous contraction of all translates preserves strong
connectivity and permits cycle lifting without a length loss. -/
theorem contraction_connectivity_and_lifting (C : Cycle D)
    (hinj : Function.Injective (fun j => (C.vertex j).2))
    (hD : ∀ g : G, ∀ x y : G × I, D (g*x.1,x.2) (g*y.1,y.2) ↔ D x y)
    (hsc : StronglyConnected D) :
    StronglyConnected (QuotientDigraph D C.contractProjection) ∧
      (∀ Q : Cycle (QuotientDigraph D C.contractProjection),
        ∃ L : Cycle D, Q.length ≤ L.length) := by
  exact ⟨quotient_stronglyConnected D C.contractProjection (C.contractProjection_surjective hinj) hsc,
    stronglyConnected_parts_cycle_lift C.contractProjection (C.contractProjection_fibres_strong hinj hD)⟩

/-- The contracted coordinate set is equivariant under left multiplication. -/
theorem contracted_graph_left_invariant (C : Cycle D)
    (hD : ∀ g : G, ∀ x y : G × I, D (g*x.1,x.2) (g*y.1,y.2) ↔ D x y)
    (g : G) (x y : G × Option C.UnusedIndices) :
    QuotientDigraph D C.contractProjection (g*x.1,x.2) (g*y.1,y.2) ↔
      QuotientDigraph D C.contractProjection x y := by
  have hf : ∀ (g : G) x y, QuotientDigraph D C.contractProjection x y →
      QuotientDigraph D C.contractProjection (g*x.1,x.2) (g*y.1,y.2) := by
    rintro g x y ⟨hne,u,v,hu,hv,huv⟩
    refine ⟨?_,(g*u.1,u.2),(g*v.1,v.2),?_,?_,(hD g u v).mpr huv⟩
    · intro he
      apply hne
      exact ((Equiv.mulLeft g).prodCongr (Equiv.refl (Option C.UnusedIndices))).injective he
    · rw [C.contractProjection_translate,hu]
    · rw [C.contractProjection_translate,hv]
  constructor
  · intro h
    have he := hf g⁻¹ _ _ h
    simpa only [inv_mul_cancel_left] using he
  · exact hf g x y

omit [Group G] in
theorem contraction_orbit_count [Finite I] (C : Cycle D)
    (hinj : Function.Injective (fun j => (C.vertex j).2)) :
    Nat.card (Option C.UnusedIndices) = Nat.card I-C.length+1 := by
  classical
  let A : Set I := Set.range (fun j => (C.vertex j).2)
  have hA : Nat.card A = C.length := by
    have he := Nat.card_congr (Equiv.ofInjective (fun j => (C.vertex j).2) hinj)
    simpa only [Nat.card_fin] using he.symm
  have hparts : Nat.card I = C.length+Nat.card C.UnusedIndices := by
    rw [← Nat.card_congr (Equiv.Set.sumCompl A),Nat.card_sum,hA]
    rfl
  let : Fintype C.UnusedIndices := Fintype.ofFinite _
  have hoption : Nat.card (Option C.UnusedIndices) = Nat.card C.UnusedIndices+1 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_option]
  rw [hoption,hparts]
  omega

end Cycle
end DirectedCycles
