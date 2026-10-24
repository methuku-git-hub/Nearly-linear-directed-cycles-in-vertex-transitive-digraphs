import DirectedCycles.LocalWordPowers
import DirectedCycles.LocalUltraproductProducts
import DirectedCycles.UltraproductListRepresentatives

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Fixed word powers commute exactly with the local reduced-product
construction, including all intermediate products and their domains. -/
theorem localUltra_wordPower_mk_iff (A : ∀ i, Set (G i)) (a : ∀ i, G i) (n : ℕ) :
    localUltraMk F G a ∈ (localUltraAlgebra F G L).wordPower (localUltraSet F G A) n ↔
      ∀ᶠ i in F, a i ∈ (L i).wordPower (A i) n := by
  classical
  constructor
  · rintro ⟨l,hlen,hl,hp⟩
    obtain ⟨v,rfl⟩ := exists_localUltra_list_representatives F G l
    have hvlen : v.length = n := by simpa only [List.length_map] using hlen
    have hv : ∀ b ∈ v.toFinset, ∀ᶠ i in F, b i ∈ A i := by
      intro b hb
      apply (localUltraMk_mem_iff F G A b).1
      exact hl _ (List.mem_map.mpr ⟨b,List.mem_toFinset.mp hb,rfl⟩)
    have hvall := (Filter.eventually_all_finset v.toFinset).2 hv
    have hprod := (localUltraProduct_mk_iff F G L v a).1 hp
    filter_upwards [hvall,hprod] with i hi hpi
    refine ⟨v.map (fun b => b i),by simpa only [List.length_map] using hvlen,?_,hpi⟩
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    exact hi b (List.mem_toFinset.mpr hb)
  · intro h
    have hc : ∀ i, ∃ l : List (G i), l.length = n ∧
        (a i ∈ (L i).wordPower (A i) n → (∀ x ∈ l, x ∈ A i) ∧ (L i).Product l (a i)) := by
      intro i
      by_cases hi : a i ∈ (L i).wordPower (A i) n
      · obtain ⟨l,hlen,hl,hp⟩ := hi
        exact ⟨l,hlen,fun _ => ⟨hl,hp⟩⟩
      · exact ⟨List.replicate n (L i).one,by simp,fun hh => (hi hh).elim⟩
    choose l hlen hl using hc
    obtain ⟨v,hvlen,hv⟩ := exists_uniform_list_representatives G l hlen
    have hh : ∀ᶠ i in F, (∀ x ∈ l i, x ∈ A i) ∧ (L i).Product (l i) (a i) := h.mono fun i hi => hl i hi
    refine ⟨v.map (localUltraMk F G),by simpa only [List.length_map] using hvlen,?_,?_⟩
    · intro x hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
      apply (localUltraMk_mem_iff F G A b).2
      filter_upwards [hh] with i hi
      apply hi.1
      rw [← hv i]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    · apply (localUltraProduct_mk_iff F G L v a).2
      filter_upwards [hh] with i hi
      rw [hv i]
      exact hi.2

theorem localUltra_wordPower (A : ∀ i, Set (G i)) (n : ℕ) :
    (localUltraAlgebra F G L).wordPower (localUltraSet F G A) n =
      localUltraSet F G (fun i => (L i).wordPower (A i) n) := by
  ext x
  induction x using Quotient.inductionOn with
  | h a =>
    rw [localUltraMk_mem_iff]
    exact localUltra_wordPower_mk_iff F G L A a n
end DirectedCycles
