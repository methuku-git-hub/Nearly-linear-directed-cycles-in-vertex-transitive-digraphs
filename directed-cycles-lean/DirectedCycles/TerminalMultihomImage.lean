module

public import DirectedCycles.MultihomSubstitution
public import DirectedCycles.LeftCommutatorGeneration
public import DirectedCycles.MultihomSubgroupWidth

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles
namespace MarkedCommutatorWord
universe u

/-- Insert a separately homomorphic image into the distinguished entry of
a terminal marked form. -/
def imageMultihom {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {B : ι → Type u} [∀ i, Group (B i)] {G : Type u} [Group G]
    (φ : GroupMultihom B G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (Set.range φ)) (w.degree+1) = ⊥) :
    GroupMultihom (fun i : Sum ι α => GroupMultihom.SumInput B G i) G :=
  (w.terminalMultihom (Subgroup.normalClosure (Set.range φ)) hw hall hnext).substituteMarked
    (Subgroup.normalClosure (Set.range φ))
    (φ.codRestrict (Subgroup.normalClosure (Set.range φ)) Subgroup.subset_normalClosure)

@[simp] theorem imageMultihom_apply {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {B : ι → Type u} [∀ i, Group (B i)] {G : Type u} [Group G]
    (φ : GroupMultihom B G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (Set.range φ)) (w.degree+1) = ⊥)
    (x : ∀ i : Sum ι α, GroupMultihom.SumInput B G i) :
    imageMultihom φ w hw hall hnext x =
      w.eval (φ (fun i => x (.inl i))) (fun i => x (.inr i)) := rfl

theorem imageMultihom_range {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {B : ι → Type u} [∀ i, Group (B i)] {G : Type u} [Group G]
    (φ : GroupMultihom B G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (Set.range φ)) (w.degree+1) = ⊥) :
    Set.range (imageMultihom φ w hw hall hnext) =
      {z | ∃ h ∈ Set.range φ, ∃ x : α → G, w.eval h x = z} := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨φ (fun i => x (.inl i)),⟨fun i => x (.inl i),rfl⟩,fun i => x (.inr i),rfl⟩
  · rintro ⟨h,⟨a,rfl⟩,x,rfl⟩
    exact ⟨(fun i => match i with | .inl j => a j | .inr j => x j),rfl⟩

theorem imageMultihom_central {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {B : ι → Type u} [∀ i, Group (B i)] {G : Type u} [Group G]
    (φ : GroupMultihom B G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (Set.range φ)) (w.degree+1) = ⊥) :
    Set.range (imageMultihom φ w hw hall hnext) ⊆ Subgroup.center G := by
  rw [imageMultihom_range]
  rintro z ⟨h,hh,x,rfl⟩
  exact relativeSeries_central_of_next_eq_bot _ _ hnext
    (w.eval_mem_relativeSeries _ h (Subgroup.subset_normalClosure hh) x)

/-- One actual separately homomorphic image generates the terminal
relative term of the original normal closure. -/
theorem imageMultihom_closure_leftList {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {B : ι → Type u} [∀ i, Group (B i)] {G : Type u} [Group G]
    (φ : GroupMultihom B G) (l : List α) (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    (hnext : relativeSeries (Subgroup.normalClosure (Set.range φ)) (l.length+1) = ⊥) :
    Subgroup.closure (Set.range (imageMultihom φ (leftList l)
      (by simpa using hl) (by simpa using hall) (by simpa using hnext))) =
      relativeSeries (Subgroup.normalClosure (Set.range φ)) l.length := by
  rw [imageMultihom_range]
  exact closure_leftList_values (Set.range φ) l hl hnext

end MarkedCommutatorWord
end DirectedCycles
