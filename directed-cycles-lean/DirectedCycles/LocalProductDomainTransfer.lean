module

public import DirectedCycles.LocalWordPowerTransfer
public import DirectedCycles.LocalUltraproductProductExistence

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Having every word of bounded length fully defined transfers in both
directions. The converse uses a bounded-length counterexample word and the
ultrafilter's finite-choice property, not an unrestricted transfer axiom. -/
theorem localUltra_allProductsDefined_iff (A : ∀ i, Set (G i)) (N : ℕ) :
    (localUltraAlgebra (U : Filter ι) G L).AllProductsDefined (localUltraSet (U : Filter ι) G A) N ↔
      ∀ᶠ i in (U : Filter ι), (L i).AllProductsDefined (A i) N := by
  classical
  constructor
  · intro h
    by_contra hn
    have hbad : ∀ᶠ i in (U : Filter ι), ¬ (L i).AllProductsDefined (A i) N :=
      Ultrafilter.eventually_not.mpr hn
    have hc : ∀ i, ∃ l : List (G i), l.length ≤ N ∧
        (¬ (L i).AllProductsDefined (A i) N →
          (∀ x ∈ l, x ∈ A i) ∧ ¬ ∃ x, (L i).Product l x) := by
      intro i
      by_cases hi : ¬ (L i).AllProductsDefined (A i) N
      · have hh : ∃ l : List (G i), l.length ≤ N ∧ (∀ x ∈ l, x ∈ A i) ∧
            ¬ ∃ x, (L i).Product l x := by
          simpa only [LocalGroupAlgebra.AllProductsDefined,not_forall,not_imp,exists_prop] using hi
        obtain ⟨l,hlen,hl,hp⟩ := hh
        exact ⟨l,hlen,fun _ => ⟨hl,hp⟩⟩
      · exact ⟨[],by simp,fun hh => (hi hh).elim⟩
    choose l hlen hl using hc
    have hexlen : ∀ᶠ i in (U : Filter ι), ∃ n : Fin (N+1), (l i).length = n.val :=
      Filter.Eventually.of_forall fun i => ⟨⟨(l i).length,by have := hlen i; omega⟩,rfl⟩
    obtain ⟨n,hn⟩ := Ultrafilter.eventually_exists_iff.mp hexlen
    let l' : ∀ i, List (G i) := fun i => if (l i).length = n.val then l i else List.replicate n.val (L i).one
    have hlen' : ∀ i, (l' i).length = n.val := by
      intro i
      dsimp only [l']
      split_ifs with hi
      · exact hi
      · simp
    have heq : ∀ᶠ i in (U : Filter ι), l' i = l i := hn.mono fun i hi => by simp only [l',ite_eq_left hi]
    obtain ⟨v,hvlen,hv⟩ := exists_uniform_list_representatives G l' hlen'
    have hmem : ∀ x ∈ v.map (localUltraMk (U : Filter ι) G), x ∈ localUltraSet (U : Filter ι) G A := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      apply (localUltraMk_mem_iff _ G A a).2
      filter_upwards [hbad,heq] with i hbi hei
      apply (hl i hbi).1
      rw [← hei,← hv i]
      exact List.mem_map.mpr ⟨a,ha,rfl⟩
    have hprod := h (v.map (localUltraMk (U : Filter ι) G))
      (by simp only [List.length_map,hvlen]; exact Nat.le_of_lt_succ n.isLt) hmem
    have hprod' := (localUltra_exists_product_iff (U : Filter ι) G L v).1 hprod
    obtain ⟨i,hbi,hei,hpi⟩ := (hbad.and (heq.and hprod')).exists
    apply (hl i hbi).2
    simpa only [hv i,hei] using hpi
  · intro h l hlen hl
    obtain ⟨v,rfl⟩ := exists_localUltra_list_representatives (U : Filter ι) G l
    have hvlen : v.length ≤ N := by simpa only [List.length_map] using hlen
    have hvmem : ∀ a ∈ v.toFinset, ∀ᶠ i in (U : Filter ι), a i ∈ A i := by
      intro a ha
      apply (localUltraMk_mem_iff _ G A a).1
      exact hl _ (List.mem_map.mpr ⟨a,List.mem_toFinset.mp ha,rfl⟩)
    have hvall := (Filter.eventually_all_finset v.toFinset).2 hvmem
    apply (localUltra_exists_product_iff (U : Filter ι) G L v).2
    filter_upwards [h,hvall] with i hi hvi
    apply hi (v.map (fun a => a i)) (by simpa only [List.length_map] using hvlen)
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact hvi a (List.mem_toFinset.mpr ha)
end DirectedCycles
