module

public import DirectedCycles.GroupMultihom

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles.GroupMultihom
variable {ι : Type*} [DecidableEq ι] {B : ι → Type*} [∀ i, Group (B i)]
  {G : Type*} [Group G]

def codComp {H : Type*} [Group H] (φ : GroupMultihom B G) (f : G →* H) :
    GroupMultihom B H where
  toFun x := f (φ x)
  map_one x i := by rw [φ.map_one,_root_.map_one]
  map_mul x i a b := by rw [φ.map_mul,_root_.map_mul]

def domComp {C : ι → Type*} [∀ i, Group (C i)] (φ : GroupMultihom B G)
    (f : ∀ i, C i →* B i) : GroupMultihom C G where
  toFun x := φ (fun i => f i (x i))
  map_one x i := by
    have he : (fun j => f j (Function.update x i 1 j)) =
        Function.update (fun j => f j (x j)) i 1 := by
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp [hji]
    rw [he,φ.map_one]
  map_mul x i a b := by
    have he : ∀ v : C i, (fun j => f j (Function.update x i v j)) =
        Function.update (fun j => f j (x j)) i (f i v) := by
      intro v
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp [hji]
    rw [he,he,he,_root_.map_mul,φ.map_mul]

theorem range_domComp {C : ι → Type*} [∀ i, Group (C i)] (φ : GroupMultihom B G)
    (f : ∀ i, C i →* B i) (hf : ∀ i, Function.Surjective (f i)) :
    Set.range (φ.domComp f) = Set.range φ := by
  ext g
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨fun i => f i (x i),rfl⟩
  · rintro ⟨x,rfl⟩
    choose y hy using fun i => hf i (x i)
    refine ⟨y,?_⟩
    change φ (fun i => f i (y i)) = φ x
    congr 1
    funext i
    exact hy i

theorem range_codComp {H : Type*} [Group H] (φ : GroupMultihom B G) (f : G →* H) :
    Set.range (φ.codComp f) = f '' Set.range φ := by
  exact Set.range_comp f φ

end DirectedCycles.GroupMultihom
