module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- Sequences equal to the identity on a filter-large set. -/
def eventuallyOne {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)] :
    Subgroup (∀ i, G i) where
  carrier := {x | ∀ᶠ i in f, x i = 1}
  one_mem' := Filter.Eventually.of_forall (fun _ => rfl)
  mul_mem' := by
    intro x y hx hy
    filter_upwards [hx,hy] with i hi hj
    change x i * y i = 1
    rw [hi,hj,mul_one]
  inv_mem' := by
    intro x hx
    filter_upwards [hx] with i hi
    change (x i)⁻¹ = 1
    rw [hi,inv_one]

instance eventuallyOne_normal {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)] :
    (eventuallyOne f G).Normal where
  conj_mem := by
    intro n hn g
    filter_upwards [hn] with i hi
    change g i * n i * (g i)⁻¹ = 1
    rw [hi,mul_one,mul_inv_cancel]

/-- The group quotient underlying an ultraproduct. The construction makes
sense for every filter; ultrafilter properties are used by transfer lemmas. -/
abbrev GroupUltraproduct {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)] :=
  (∀ i, G i) ⧸ eventuallyOne f G

def ultraMk {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)] :
    (∀ i, G i) →* GroupUltraproduct f G := QuotientGroup.mk' (eventuallyOne f G)

theorem ultraMk_surjective {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)] :
    Function.Surjective (ultraMk f G) := QuotientGroup.mk'_surjective _

theorem ultraMk_eq_iff {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (x y : ∀ i, G i) : ultraMk f G x = ultraMk f G y ↔ ∀ᶠ i in f, x i = y i := by
  let q := ultraMk f G
  constructor
  · intro he
    have hk : x⁻¹*y ∈ eventuallyOne f G := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (x⁻¹*y) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    filter_upwards [hk] with i hi
    change (x i)⁻¹*y i = 1 at hi
    exact inv_mul_eq_one.mp hi
  · intro he
    have hk : x⁻¹*y ∈ eventuallyOne f G := by
      filter_upwards [he] with i hi
      change (x i)⁻¹*y i = 1
      rw [hi,inv_mul_cancel]
    have hq : q (x⁻¹*y) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    rw [map_mul,map_inv] at hq
    exact inv_mul_eq_one.mp hq

/-- The internal set represented by a family of subsets. -/
def ultraSet {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) : Set (GroupUltraproduct f G) :=
  (ultraMk f G) '' {x | ∀ᶠ i in f, x i ∈ A i}

theorem ultraMk_mem_ultraSet_iff {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) (x : ∀ i, G i) :
    ultraMk f G x ∈ ultraSet f G A ↔ ∀ᶠ i in f, x i ∈ A i := by
  constructor
  · rintro ⟨y,hy,he⟩
    have hh := (ultraMk_eq_iff f G y x).mp he
    filter_upwards [hy,hh] with i hi heq
    rwa [← heq]
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem ultraSet_mono {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A B : ∀ i, Set (G i)) (h : ∀ᶠ i in f, A i ⊆ B i) :
    ultraSet f G A ⊆ ultraSet f G B := by
  rintro z ⟨x,hx,rfl⟩
  apply (ultraMk_mem_ultraSet_iff f G B x).mpr
  filter_upwards [hx,h] with i hi hsub
  exact hsub hi

end DirectedCycles
