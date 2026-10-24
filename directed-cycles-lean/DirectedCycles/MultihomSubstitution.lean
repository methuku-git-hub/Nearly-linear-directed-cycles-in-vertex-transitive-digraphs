import DirectedCycles.TerminalCommutatorMaps

set_option autoImplicit false
namespace DirectedCycles
namespace GroupMultihom
universe u

/-- Two blocks of input groups. -/
abbrev SumInput {ι κ : Type*} (B : ι → Type u) (G : Type u) : Sum ι κ → Type _
  | .inl i => B i
  | .inr _ => G

instance sumInputGroup {ι κ : Type*} (B : ι → Type u) [∀ i, Group (B i)]
    (G : Type u) [Group G] (i : Sum ι κ) : Group (SumInput B G i) := by
  cases i <;> infer_instance

/-- The tuple passed to a marked map when its distinguished input is
itself a separately homomorphic map. -/
def markedTuple {ι α : Type*} [DecidableEq ι] {B : ι → Type u} [∀ i, Group (B i)]
    {G : Type u} [Group G] (N : Subgroup G) (φ : GroupMultihom B N)
    (x : ∀ i : Sum ι α, SumInput B G i) : ∀ i, MarkedCommutatorWord.Input N α i
  | none => φ (fun i => x (.inl i))
  | some j => x (.inr j)

theorem markedTuple_update_left {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {B : ι → Type u} [∀ i, Group (B i)] {G : Type u} [Group G]
    (N : Subgroup G) (φ : GroupMultihom B N)
    (x : ∀ i : Sum ι α, SumInput B G i) (i : ι) (a : B i) :
    markedTuple N φ (Function.update x (.inl i) a) =
      Function.update (markedTuple N φ x) none
        (φ (Function.update (fun j => x (.inl j)) i a)) := by
  funext j
  cases j with
  | none =>
    simp only [markedTuple,Function.update_self]
    congr 1
    funext k
    by_cases h : k = i
    · subst k; simp
    · simp [h]
  | some j => simp [markedTuple]

theorem markedTuple_update_right {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {B : ι → Type u} [∀ i, Group (B i)] {G : Type u} [Group G]
    (N : Subgroup G) (φ : GroupMultihom B N)
    (x : ∀ i : Sum ι α, SumInput B G i) (i : α) (a : G) :
    markedTuple N φ (Function.update x (.inr i) a) =
      Function.update (markedTuple N φ x) (some i) a := by
  funext j
  cases j with
  | none => simp [markedTuple]
  | some j =>
    by_cases h : j = i
    · subst j; simp [markedTuple]
    · simp [markedTuple,h]

/-- Composition into the distinguished coordinate preserves separate
homomorphism laws. The inner and outer laws are both proved data. -/
def substituteMarked {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {B : ι → Type u} [∀ i, Group (B i)] {G : Type u} [Group G]
    {T : Type*} [Group T] (N : Subgroup G)
    (ψ : GroupMultihom (MarkedCommutatorWord.Input N α) T) (φ : GroupMultihom B N) :
    GroupMultihom (fun i : Sum ι α => SumInput B G i) T where
  toFun x := ψ (markedTuple N φ x)
  map_one x i := by
    cases i with
    | inl i => rw [markedTuple_update_left,φ.map_one]; exact ψ.map_one _ none
    | inr i => rw [markedTuple_update_right]; exact ψ.map_one _ (some i)
  map_mul x i a b := by
    cases i with
    | inl i =>
      rw [markedTuple_update_left,markedTuple_update_left,markedTuple_update_left,φ.map_mul]
      exact ψ.map_mul _ none _ _
    | inr i =>
      rw [markedTuple_update_right,markedTuple_update_right,markedTuple_update_right]
      exact ψ.map_mul _ (some i) _ _

end GroupMultihom
end DirectedCycles
