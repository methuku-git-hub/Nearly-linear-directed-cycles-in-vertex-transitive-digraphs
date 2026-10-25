module

public import DirectedCycles.LocalGroupUltraproduct

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- The domain of the actual reduced-product multiplication is exactly eventual
membership in the component multiplication domains. -/
theorem localUltra_defined_mk_iff (a b : ∀ i, G i) :
    (localUltraAlgebra F G L).Defined (localUltraMk F G a) (localUltraMk F G b) ↔
      ∀ᶠ i in F, (L i).Defined (a i) (b i) := by
  classical
  constructor
  · rintro ⟨z,hz⟩
    induction z using Quotient.inductionOn with
    | h c =>
      have hc := (localUltraMulRel_mk_iff F G L a b c).1 hz
      exact hc.mono fun _ hi => ⟨_,hi⟩
  · intro h
    let c : ∀ i, G i := fun i => if hi : (L i).Defined (a i) (b i)
      then (L i).mul (a i) (b i) hi else (L i).one
    refine ⟨localUltraMk F G c,(localUltraMulRel_mk_iff F G L a b c).2 ?_⟩
    filter_upwards [h] with i hi
    dsimp only [c]
    rw [dite_eq_left hi]
    exact (L i).mul_spec _ _ hi

/-- Internal sets in the actual local-group reduced product. -/
def localUltraSet (A : ∀ i, Set (G i)) : Set (LocalUltraproduct F G) :=
  (localUltraMk F G) '' {a | ∀ᶠ i in F, a i ∈ A i}

theorem localUltraMk_mem_iff (A : ∀ i, Set (G i)) (a : ∀ i, G i) :
    localUltraMk F G a ∈ localUltraSet F G A ↔ ∀ᶠ i in F, a i ∈ A i := by
  constructor
  · rintro ⟨b,hb,he⟩
    have he' := (localUltraMk_eq_iff F G b a).1 he
    filter_upwards [hb,he'] with i hi hei
    simpa only [← hei] using hi
  · exact fun h => ⟨a,h,rfl⟩

/-- Pointwise multiplication uses only defined products. -/
def LocalGroupAlgebra.setMul {X : Type*} (L : LocalGroupAlgebra X) (A B : Set X) : Set X :=
  {z | ∃ a ∈ A, ∃ b ∈ B, L.mulRel a b z}

theorem localUltraSet_mul (A B : ∀ i, Set (G i)) :
    localUltraSet F G (fun i => (L i).setMul (A i) (B i)) =
      (localUltraAlgebra F G L).setMul (localUltraSet F G A) (localUltraSet F G B) := by
  classical
  ext z
  induction z using Quotient.inductionOn with
  | h c =>
    constructor
    · intro hc
      have h := (localUltraMk_mem_iff F G _ c).1 hc
      let a : ∀ i, G i := fun i => if hi : c i ∈ (L i).setMul (A i) (B i)
        then Classical.choose hi else (L i).one
      let b : ∀ i, G i := fun i => if hi : c i ∈ (L i).setMul (A i) (B i)
        then Classical.choose (Classical.choose_spec hi).2 else (L i).one
      have ha : ∀ᶠ i in F, a i ∈ A i := by
        filter_upwards [h] with i hi
        dsimp [a]
        rw [dite_eq_left hi]
        exact (Classical.choose_spec hi).1
      have hb : ∀ᶠ i in F, b i ∈ B i := by
        filter_upwards [h] with i hi
        dsimp [b]
        rw [dite_eq_left hi]
        exact (Classical.choose_spec (Classical.choose_spec hi).2).1
      have hab : ∀ᶠ i in F, (L i).mulRel (a i) (b i) (c i) := by
        filter_upwards [h] with i hi
        dsimp [a,b]
        rw [dite_eq_left hi,dite_eq_left hi]
        exact (Classical.choose_spec (Classical.choose_spec hi).2).2
      exact ⟨localUltraMk F G a,(localUltraMk_mem_iff F G A a).2 ha,
        localUltraMk F G b,(localUltraMk_mem_iff F G B b).2 hb,
          (localUltraMulRel_mk_iff F G L a b c).2 hab⟩
    · rintro ⟨x,⟨a,ha,rfl⟩,y,⟨b,hb,rfl⟩,hab⟩
      apply (localUltraMk_mem_iff F G _ c).2
      have hab' := (localUltraMulRel_mk_iff F G L a b c).1 hab
      filter_upwards [ha,hb,hab'] with i hai hbi habi
      exact ⟨a i,hai,b i,hbi,habi⟩
end DirectedCycles
