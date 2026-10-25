module

public import DirectedCycles.LocalProgressionFamilyChoice
public import DirectedCycles.LocalLargeIndex

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- The quantitative conclusion used in Lie-dimension induction. All
progression witnesses are actual finite local words, and every retained
coordinate length diverges along the given filter. -/
def HasLargeLocalProgressions {ι : Type*} (F : Filter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i)) (A : ∀ i, Set (G i)) (a : ι → ℕ) : Prop :=
  ∃ r c J : ℕ, 1 ≤ J ∧ ∃ N : ι → Fin r → ℕ,
    (∀ j, Filter.Tendsto (fun i => N i j) F Filter.atTop) ∧
    ∀ᶠ i in F, ∃ W : (L i).ProgressionWitness (A i) r c,
      W.lengths = N i ∧ a i ≤ J * ∏ j, (2*W.lengths j+1)

namespace HasLargeLocalProgressions
variable {ι : Type*} {F : Filter ι} {G : ι → Type*} {L : ∀ i, LocalGroupAlgebra (G i)}
    {A B : ∀ i, Set (G i)} {a b : ι → ℕ}

/-- Uniform source density and containment transfer the same concrete
progression family to the larger source. -/
theorem of_containment_density (h : HasLargeLocalProgressions F G L B b)
    {J₀ : ℕ} (hJ₀ : 1 ≤ J₀) (hBA : ∀ᶠ i in F, B i ⊆ A i)
    (hdensity : ∀ᶠ i in F, a i ≤ J₀*b i) : HasLargeLocalProgressions F G L A a := by
  obtain ⟨r,c,J,hJ,N,hN,hW⟩ := h
  refine ⟨r,c,J₀*J,by nlinarith,N,hN,?_⟩
  filter_upwards [hW,hBA,hdensity] with i hi hbi hdi
  obtain ⟨W,hWi,hcard⟩ := hi
  refine ⟨W.mono hbi,hWi,?_⟩
  change a i ≤ J₀*J * ∏ j, (2*W.lengths j+1)
  exact hdi.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left J₀ hcard)

/-- An eventually bounded source has the rank-zero identity progression,
with no spurious divergent coordinate required. -/
theorem of_bounded_card (hA : ∀ᶠ i in F, (L i).one ∈ A i)
    {J : ℕ} (hJ : 1 ≤ J) (ha : ∀ᶠ i in F, a i ≤ J) : HasLargeLocalProgressions F G L A a := by
  refine ⟨0,0,J,hJ,fun _ => Fin.elim0,fun j => Fin.elim0 j,?_⟩
  filter_upwards [hA,ha] with i hi hai
  refine ⟨(L i).identityProgressionWitness.mono (Set.singleton_subset_iff.mpr hi),?_,?_⟩
  · funext j
    exact Fin.elim0 j
  · simpa only [Fin.prod_univ_zero,Nat.mul_one] using hai

/-- Restricting to an ultrafilter-large index set loses no progression
conclusion. Outside that set only the length functions are extended; no
false finite progression assertion is made on discarded components. -/
theorem of_largeIndex (U : Ultrafilter ι) (s : Set ι) (hs : s ∈ U)
    (h : HasLargeLocalProgressions (localLargeIndexUltrafilter U s hs : Filter s)
      (fun j => G j.val) (fun j => L j.val) (fun j => A j.val) (fun j => a j.val)) :
    HasLargeLocalProgressions (U : Filter ι) G L A a := by
  classical
  obtain ⟨r,c,J,hJ,N,hN,hW⟩ := h
  let N' : ι → Fin r → ℕ := fun i => if hi : i ∈ s then N ⟨i,hi⟩ else fun _ => 1
  have hN' : ∀ j, Filter.Tendsto (fun i => N' i j) (U : Filter ι) Filter.atTop := by
    intro j
    apply Filter.tendsto_atTop.2
    intro m
    have hh := (localLargeIndex_eventually_iff U s hs (fun i => m ≤ N i j)).1
      ((Filter.tendsto_atTop.1 (hN j)) m)
    filter_upwards [hh,hs] with i hi hsi
    simpa only [N',dite_eq_left hsi] using hi hsi
  refine ⟨r,c,J,hJ,N',hN',?_⟩
  have hh := (localLargeIndex_eventually_iff U s hs _).1 hW
  filter_upwards [hh,hs] with i hi hsi
  simpa only [N',dite_eq_left hsi] using hi hsi
end HasLargeLocalProgressions
end DirectedCycles
