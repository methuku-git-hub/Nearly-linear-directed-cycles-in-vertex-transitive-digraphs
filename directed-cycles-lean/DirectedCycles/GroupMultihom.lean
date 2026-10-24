import DirectedCycles.PGroupUnionWidth

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- A group-valued map which is a homomorphism separately in each variable.
The two laws are part of the definition of this mathematical object. -/
structure GroupMultihom {ι : Type*} [DecidableEq ι] (B : ι → Type*)
    [∀ i, Group (B i)] (G : Type*) [Group G] where
  toFun : (∀ i, B i) → G
  map_one : ∀ x i, toFun (Function.update x i 1) = 1
  map_mul : ∀ x i a b, toFun (Function.update x i (a*b)) =
    toFun (Function.update x i a) * toFun (Function.update x i b)

instance {ι : Type*} [DecidableEq ι] {B : ι → Type*} [∀ i, Group (B i)]
    {G : Type*} [Group G] : CoeFun (GroupMultihom B G) (fun _ => (∀ i, B i) → G) :=
  ⟨GroupMultihom.toFun⟩

namespace GroupMultihom
variable {ι : Type*} [DecidableEq ι] {B : ι → Type*} [∀ i, Group (B i)]
  {G : Type*} [Group G]

def slice (φ : GroupMultihom B G) (x : ∀ i, B i) (i : ι) : B i →* G where
  toFun a := φ (Function.update x i a)
  map_one' := φ.map_one x i
  map_mul' := φ.map_mul x i

@[simp] theorem slice_apply_self (φ : GroupMultihom B G) (x : ∀ i, B i) (i : ι) :
    φ.slice x i (x i) = φ x := by simp [slice]

theorem one_mem_range [Nonempty ι] (φ : GroupMultihom B G) : 1 ∈ Set.range φ := by
  let i : ι := Classical.choice inferInstance
  exact ⟨Function.update (fun _ => 1) i 1,φ.map_one _ i⟩

theorem zpowers_subset_range [Nonempty ι] (φ : GroupMultihom B G) (x : G)
    (hx : x ∈ Set.range φ) : (Subgroup.zpowers x : Set G) ⊆ Set.range φ := by
  let i : ι := Classical.choice inferInstance
  obtain ⟨a,rfl⟩ := hx
  intro g hg
  obtain ⟨z,rfl⟩ := hg
  refine ⟨Function.update a i (a i ^ z),?_⟩
  exact (map_zpow (φ.slice a i) (a i) z).trans (congrArg (fun x => x^z) (φ.slice_apply_self a i))

/-- Finite Tointon Lemma 6.2. The source groups need no additional
nilpotency assumption for this p-group target case. -/
theorem pgroup_range_width {G : Type*} [CommGroup G] [Finite G] [Nonempty ι]
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p G) (φ : GroupMultihom B G) :
    (Subgroup.closure (Set.range φ) : Set G) ⊆ (Set.range φ)^(Group.rank G) :=
  pgroup_union_subgroups_width p hP (Set.range φ) φ.one_mem_range φ.zpowers_subset_range

end GroupMultihom
end DirectedCycles
