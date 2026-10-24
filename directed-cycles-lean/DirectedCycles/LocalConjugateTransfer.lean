import DirectedCycles.LocalConjugates
import DirectedCycles.LocalUltraproductProducts
import DirectedCycles.LocalInternalSetLogic

set_option autoImplicit false
namespace DirectedCycles
theorem localUltra_inv_mk_filter {ι : Type*} (F : Filter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i)) (b : ∀ i, G i) :
    (localUltraAlgebra F G L).inv (localUltraMk F G b) =
      localUltraMk F G (fun i => (L i).inv (b i)) := rfl

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Conjugation sets transfer exactly, retaining the repeated conjugating
element and the actual all-bracketings triple product. -/
theorem localUltra_conjugates (S B : ∀ i, Set (G i)) :
    (localUltraAlgebra (U : Filter ι) G L).conjugates
      (localUltraSet (U : Filter ι) G S) (localUltraSet (U : Filter ι) G B) =
      localUltraSet (U : Filter ι) G (fun i => (L i).conjugates (S i) (B i)) := by
  classical
  let F : Filter ι := U
  ext x
  obtain ⟨a,rfl⟩ := Quotient.exists_rep x
  constructor
  · rintro ⟨s,hs,b,hb,hp⟩
    obtain ⟨s,rfl⟩ := Quotient.exists_rep s
    obtain ⟨b,rfl⟩ := Quotient.exists_rep b
    have hprod : ∀ᶠ i in F, (L i).Product [(L i).inv (b i),s i,b i] (a i) := by
      have ht := (localUltraProduct_mk_iff F G L [fun i => (L i).inv (b i),s,b] a).1
        (by simpa only [List.map_cons,List.map_nil,localUltra_inv_mk_filter] using hp)
      simpa only [List.map_cons,List.map_nil] using ht
    apply (localUltraMk_mem_iff F G _ a).2
    filter_upwards [(localUltraMk_mem_iff F G S s).1 hs,
      (localUltraMk_mem_iff F G B b).1 hb,hprod] with i hsi hbi hpi
    exact ⟨s i,hsi,b i,hbi,hpi⟩
  · intro h
    have hh := (localUltraMk_mem_iff F G _ a).1 h
    have hex : ∀ i, ∃ s b : G i, (a i ∈ (L i).conjugates (S i) (B i) →
        s ∈ S i ∧ b ∈ B i ∧ (L i).Product [(L i).inv b,s,b] (a i)) := by
      intro i
      by_cases hi : a i ∈ (L i).conjugates (S i) (B i)
      · obtain ⟨s,hs,b,hb,hp⟩ := hi
        exact ⟨s,b,fun _ => ⟨hs,hb,hp⟩⟩
      · exact ⟨(L i).one,(L i).one,fun hi' => (hi hi').elim⟩
    choose s b hsb using hex
    have hw := hh.mono fun i hi => hsb i hi
    refine ⟨localUltraMk F G s,(localUltraMk_mem_iff F G S s).2 (hw.mono fun _ hi => hi.1),
      localUltraMk F G b,(localUltraMk_mem_iff F G B b).2 (hw.mono fun _ hi => hi.2.1),?_⟩
    have hp := (localUltraProduct_mk_iff F G L [fun i => (L i).inv (b i),s,b] a).2
      (by simpa only [List.map_cons,List.map_nil] using hw.mono (fun _ hi => hi.2.2))
    simpa only [F,List.map_cons,List.map_nil,localUltra_inv_mk_filter] using hp
end DirectedCycles
