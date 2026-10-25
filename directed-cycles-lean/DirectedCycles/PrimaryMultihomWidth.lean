module

public import DirectedCycles.GroupMultihomOperations
public import DirectedCycles.PrimeComponentHom
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Finitely many coordinatewise replacements determine a function's value. -/
theorem finite_function_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ι → Type*} {C : Type*} (f : (∀ i, B i) → C) (x y : ∀ i, B i)
    (h : ∀ z i, f z = f (Function.update z i (y i))) : f x = f y := by
  classical
  have hh : ∀ s : Finset ι, f x = f (fun i => if i ∈ s then y i else x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [ih,h _ i]
      congr 1
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp [hji]
  simpa using hh Finset.univ

namespace GroupMultihom
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {B : ι → κ → Type*} [∀ i j, Group (B i j)]
  {G : κ → Type*} [∀ j, CommGroup (G j)]

theorem primary_coordinate_eq (p : κ → ℕ) (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) (hB : ∀ i j, IsPGroup (p j) (B i j))
    (hG : ∀ j, IsPGroup (p j) (G j))
    (φ : GroupMultihom (fun i => ∀ j, B i j) (∀ j, G j))
    (j : κ) (x y : ∀ i j, B i j) (he : ∀ i, x i j = y i j) : φ x j = φ y j := by
  let ψ := φ.codComp (Pi.evalMonoidHom G j)
  have hh : ∀ z i v, z i j = v j → ψ z = ψ (Function.update z i v) := by
    intro z i v hv
    have h1 := primary_product_hom_coordinate p hp hinj (hB i) j (hG j) (ψ.slice z i) (z i)
    have h2 := primary_product_hom_coordinate p hp hinj (hB i) j (hG j) (ψ.slice z i) v
    rw [hv] at h1
    exact (ψ.slice_apply_self z i).symm.trans (h1.trans h2.symm)
  have hh' : ∀ s : Finset ι, ψ x = ψ (fun i => if i ∈ s then y i else x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [ih,hh _ i (y i) (by simpa [hi] using he i)]
      congr 1
      funext k
      by_cases hki : k = i
      · subst k; simp
      · simp [hki]
  change ψ x = ψ y
  simpa using hh' Finset.univ

theorem primary_range_eq_pi (p : κ → ℕ) (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) (hB : ∀ i j, IsPGroup (p j) (B i j))
    (hG : ∀ j, IsPGroup (p j) (G j))
    (φ : GroupMultihom (fun i => ∀ j, B i j) (∀ j, G j)) :
    Set.range φ = Set.pi Set.univ (fun j => Set.range (φ.codComp (Pi.evalMonoidHom G j))) := by
  classical
  ext g
  constructor
  · rintro ⟨x,rfl⟩ j _
    exact ⟨x,rfl⟩
  · intro hg
    have hh : ∀ j, ∃ x : ∀ i j, B i j, φ x j = g j := fun j => hg j (Set.mem_univ j)
    choose x hx using hh
    refine ⟨fun i j => x j i j,?_⟩
    funext j
    exact (primary_coordinate_eq p hp hinj hB hG φ j (fun i k => x k i k) (x j) (fun _ => rfl)).trans (hx j)

/-- Coordinatewise p-group bounds combine without a factor for the number
of primes: each product position is assembled into one multilinear image. -/
theorem primary_product_range_width [Nonempty ι] [∀ j, Finite (G j)]
    (p : κ → ℕ) (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) (hB : ∀ i j, IsPGroup (p j) (B i j))
    (hG : ∀ j, IsPGroup (p j) (G j)) (r : ℕ) (hr : ∀ j, Group.rank (G j) ≤ r)
    (φ : GroupMultihom (fun i => ∀ j, B i j) (∀ j, G j)) :
    (Subgroup.closure (Set.range φ) : Set (∀ j, G j)) ⊆ (Set.range φ)^r := by
  classical
  intro g hg
  let ψ := fun j => φ.codComp (Pi.evalMonoidHom G j)
  have hmem : ∀ j, g j ∈ (Set.range (ψ j))^r := by
    intro j
    let : Fact (p j).Prime := ⟨hp j⟩
    have hm : g j ∈ Subgroup.closure (Set.range (ψ j)) := by
      have hh : g j ∈ (Subgroup.closure (Set.range φ)).map (Pi.evalMonoidHom G j) := ⟨g,hg,rfl⟩
      rw [MonoidHom.map_closure,← range_codComp] at hh
      exact hh
    exact Set.pow_subset_pow_right (ψ j).one_mem_range (hr j)
      (pgroup_range_width (p j) (hG j) (ψ j) hm)
  have hex : ∀ j, ∃ f : Fin r → G j, (∀ i, f i ∈ Set.range (ψ j)) ∧ ∏ i, f i = g j :=
    fun j => Set.mem_pow_iff_prod.mp (hmem j)
  choose f hf hprod using hex
  apply Set.mem_pow_iff_prod.mpr
  refine ⟨fun i j => f j i,?_,?_⟩
  · intro i
    rw [primary_range_eq_pi p hp hinj hB hG]
    exact fun j _ => hf j i
  · funext j
    simpa using hprod j

end GroupMultihom
end DirectedCycles
