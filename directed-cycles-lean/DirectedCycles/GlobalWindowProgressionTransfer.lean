module

public import DirectedCycles.LocalWordWitnessImage
public import DirectedCycles.LocalGeneratorCommutatorRestriction
public import DirectedCycles.LocalProgressionInductionProperty

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles.LocalGroupAlgebra

/-- A sufficiently long local word box in an actual global window has the
same ambient nilpotence laws. The word budget certifies every intermediate
commutator before the local vanishing assertion is applied. -/
noncomputable def ProgressionWitness.globalWindowImage {G : Type*} [Group G]
    (S : Set G) (h1 : (1 : G) ∈ S) (hi : ∀ x ∈ S, x⁻¹ ∈ S)
    {A : Set S} {r c : ℕ}
    (W : ((ofGroup G).restrict S h1 hi).ProgressionWitness A r c)
    (hbudget : ∀ i, 4^(c+1) ≤ W.lengths i) :
    (ofGroup G).ProgressionWitness (Subtype.val '' A) r c := by
  let f := LocalGroupHom.inclusion (ofGroup G) S h1 hi
  have hw := W.words.image f
  refine ⟨fun i => (W.generators i).val,W.lengths,W.lengths_pos,hw,
    orderedGrid_image_injective W.words f Subtype.val_injective W.proper,?_⟩
  intro x hx
  have hall : (ofGroup G).SignedWordsIn (fun i => (W.generators i).val) W.lengths S :=
    hw.mono (ofGroup G) (fun _ => le_rfl) (by rintro _ ⟨y,_hy,rfl⟩; exact y.property)
  obtain ⟨y,hy,hcy⟩ := generatorCommutators_restrict (ofGroup G) (ofGroup_reversible G)
    S h1 hi W.generators W.lengths hall c hbudget c le_rfl x hx
  have hy1 := W.commutators y hcy
  exact hy.symm.trans (congrArg Subtype.val hy1)
end DirectedCycles.LocalGroupAlgebra

namespace DirectedCycles.HasLargeLocalProgressions

/-- Diverging lengths eventually supply the bounded-depth ambient
commutator budget, so the entire local induction conclusion transfers to
the original finite groups. -/
theorem globalWindowImage {ι : Type*} {F : Filter ι} {G : ι → Type*} [∀ i, Group (G i)]
    (S : ∀ i, Set (G i)) (h1 : ∀ i, (1 : G i) ∈ S i)
    (hi : ∀ i, ∀ x ∈ S i, x⁻¹ ∈ S i)
    {A : ∀ i, Set (S i)} {a : ι → ℕ}
    (h : HasLargeLocalProgressions F (fun i => S i)
      (fun i => (LocalGroupAlgebra.ofGroup (G i)).restrict (S i) (h1 i) (hi i)) A a) :
    HasLargeLocalProgressions F G (fun i => LocalGroupAlgebra.ofGroup (G i))
      (fun i => Subtype.val '' A i) a := by
  obtain ⟨r,c,J,hJ,N,hN,hW⟩ := h
  have hbudget : ∀ᶠ i in F, ∀ j, 4^(c+1) ≤ N i j :=
    Filter.eventually_all.2 (fun j => (hN j).eventually (Filter.eventually_ge_atTop _))
  refine ⟨r,c,J,hJ,N,hN,?_⟩
  filter_upwards [hW,hbudget] with i hwi hbi
  obtain ⟨W,hWN,hcard⟩ := hwi
  have hb : ∀ j, 4^(c+1) ≤ W.lengths j := by simpa only [hWN] using hbi
  exact ⟨W.globalWindowImage (S i) (h1 i) (hi i) hb,hWN,hcard⟩
end DirectedCycles.HasLargeLocalProgressions
