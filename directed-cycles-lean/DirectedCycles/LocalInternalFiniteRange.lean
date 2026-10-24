import DirectedCycles.LocalInternalImages
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- A finite range is represented exactly by its component finite ranges. -/
theorem localUltraSet_finite_range {ι J : Type*} [Finite J] (u : Ultrafilter ι)
    (G : ι → Type*) (a : J → ∀ i, G i) :
    localUltraSet (u : Filter ι) G (fun i => Set.range (fun j => a j i)) =
      Set.range (fun j => localUltraMk (u : Filter ι) G (a j)) := by
  ext x
  obtain ⟨b,rfl⟩ := Quotient.mk_surjective x
  rw [localUltraMk_mem_iff]
  constructor
  · intro h
    have he : ∀ᶠ i in (u : Filter ι), ∃ j, a j i = b i := h
    obtain ⟨j,hj⟩ := (u.eventually_exists_iff).1 he
    exact ⟨j,Quotient.sound hj⟩
  · rintro ⟨j,hj⟩
    have he := (localUltraMk_eq_iff _ G _ _).1 hj
    exact he.mono fun i hi => ⟨j,hi⟩

/-- Exact bounded enumeration pads by an existing member, so it does not add
an extra covering element. -/
theorem finset_bounded_enumeration {G : Type*} (X : Finset G) (hX : X.Nonempty)
    (N : ℕ) (hN : X.card ≤ N) : ∃ a : Fin N → G, Set.range a = (X : Set G) := by
  classical
  obtain ⟨e,he⟩ := hX
  let q := Fintype.equivFin X
  let a : Fin N → G := fun j => if h : j.val < Fintype.card X then (q.symm ⟨j.val,h⟩).val else e
  refine ⟨a,Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨j,rfl⟩
    dsimp only [a]
    split
    · exact (q.symm _).property
    · exact he
  · intro x hx
    let j := q ⟨x,hx⟩
    have hj : j.val < N := j.isLt.trans_le (by simpa only [Fintype.card_coe] using hN)
    refine ⟨⟨j.val,hj⟩,?_⟩
    dsimp only [a]
    rw [dite_eq_left j.isLt]
    exact congrArg Subtype.val (q.symm_apply_apply ⟨x,hx⟩)

/-- Uniform finite nonempty internal sets have an actual finite realization
of at most the same cardinality. -/
theorem localUltraSet_finite_of_bound {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) (X : ∀ i, Finset (G i)) (N : ℕ)
    (hX : ∀ i, (X i).Nonempty) (hN : ∀ i, (X i).card ≤ N) :
    ∃ E : Finset (LocalUltraproduct (u : Filter ι) G), E.card ≤ N ∧
      (E : Set _) = localUltraSet (u : Filter ι) G (fun i => (X i : Set (G i))) := by
  classical
  choose a ha using fun i => finset_bounded_enumeration (X i) (hX i) N (hN i)
  let b := fun j => localUltraMk (u : Filter ι) G (fun i => a i j)
  refine ⟨Finset.univ.image b,?_,?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · simp only [Finset.coe_image,Finset.coe_univ,Set.image_univ]
    rw [← localUltraSet_finite_range]
    congr 1
    funext i
    exact ha i
end DirectedCycles
