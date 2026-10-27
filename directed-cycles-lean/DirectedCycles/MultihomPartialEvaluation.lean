module

public import DirectedCycles.MultihomSubgroupWidth

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles.GroupMultihom

/-- Fill inactive coordinates with fixed values. -/
def fillInputs {ι : Type*} {B : ι → Type*} (s : Set ι) [DecidablePred (· ∈ s)]
    (x : ∀ i, B i) (z : ∀ i : s, B i.val) (i : ι) : B i :=
  if hi : i ∈ s then z ⟨i,hi⟩ else x i

theorem fillInputs_update {ι : Type*} [DecidableEq ι] {B : ι → Type*}
    (s : Set ι) [DecidablePred (· ∈ s)] (x : ∀ i, B i) (z : ∀ i : s, B i.val)
    (i : s) (a : B i.val) :
    fillInputs s x (Function.update z i a) = Function.update (fillInputs s x z) i.val a := by
  funext j
  by_cases hji : j = i.val
  · subst j; simp [fillInputs,i.property]
  · by_cases hj : j ∈ s
    · have hne : (⟨j,hj⟩ : s) ≠ i := by intro h; exact hji (congrArg Subtype.val h)
      simp [fillInputs,hji,hj,hne]
    · simp [fillInputs,hji,hj]

/-- Fix any collection of coordinates; the remaining map is still a
homomorphism separately in each active variable. -/
def partialEvaluation {ι : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (s : Set ι) [DecidablePred (· ∈ s)] (x : ∀ i, B i) :
    GroupMultihom (fun i : s => B i.val) G where
  toFun z := φ (fillInputs s x z)
  map_one z i := by rw [fillInputs_update]; exact φ.map_one _ i.val
  map_mul z i a b := by rw [fillInputs_update,fillInputs_update,fillInputs_update]; exact φ.map_mul _ i.val _ _

@[simp] theorem partialEvaluation_apply {ι : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (s : Set ι) [DecidablePred (· ∈ s)] (x : ∀ i, B i)
    (z : ∀ i : s, B i.val) : φ.partialEvaluation s x z = φ (fillInputs s x z) := rfl

/-- Restrict every coordinate to an actual subgroup. -/
def subgroupDom {ι : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (H : ∀ i, Subgroup (B i)) : GroupMultihom (fun i => H i) G :=
  φ.domComp (fun i => (H i).subtype)

@[simp] theorem subgroupDom_apply {ι : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (φ : GroupMultihom B G) (H : ∀ i, Subgroup (B i)) (x : ∀ i, H i) :
    φ.subgroupDom H x = φ (fun i => (x i).val) := rfl

end DirectedCycles.GroupMultihom
