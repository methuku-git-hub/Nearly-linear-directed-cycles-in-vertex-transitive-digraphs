module

public import DirectedCycles.TerminalMultihomImage
public import DirectedCycles.RelativeSeriesQuotients

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace MarkedCommutatorWord

/-- The distinguished entry lies in the original subgroup H; its normal
closure is used only for the relative central-series argument. -/
def subgroupTerminalMultihom {α : Type*} [DecidableEq α] {G : Type*} [Group G]
    (H : Subgroup G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (H : Set G)) (w.degree+1) = ⊥) :
    GroupMultihom (Input H α) G :=
  (w.terminalMultihom (Subgroup.normalClosure (H : Set G)) hw hall hnext).domComp
    (fun i => match i with
      | none => Subgroup.inclusion Subgroup.le_normalClosure
      | some _ => MonoidHom.id G)

@[simp] theorem subgroupTerminalMultihom_apply {α : Type*} [DecidableEq α]
    {G : Type*} [Group G] (H : Subgroup G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (H : Set G)) (w.degree+1) = ⊥)
    (x : ∀ i, Input H α i) :
    subgroupTerminalMultihom H w hw hall hnext x = w.eval (x none).val (fun i => x (some i)) := rfl

theorem subgroupTerminalMultihom_range {α : Type*} [DecidableEq α]
    {G : Type*} [Group G] (H : Subgroup G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (H : Set G)) (w.degree+1) = ⊥) :
    Set.range (subgroupTerminalMultihom H w hw hall hnext) =
      {z | ∃ h ∈ H, ∃ x : α → G, w.eval h x = z} := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(x none).val,(x none).property,fun i => x (some i),rfl⟩
  · rintro ⟨h,hh,x,rfl⟩
    exact ⟨(fun i => match i with | none => ⟨h,hh⟩ | some j => x j),rfl⟩

theorem subgroupTerminalMultihom_central {α : Type*} [DecidableEq α]
    {G : Type*} [Group G] (H : Subgroup G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (H : Set G)) (w.degree+1) = ⊥) :
    Set.range (subgroupTerminalMultihom H w hw hall hnext) ⊆ Subgroup.center G := by
  rw [subgroupTerminalMultihom_range]
  rintro z ⟨h,hh,x,rfl⟩
  exact relativeSeries_central_of_next_eq_bot _ _ hnext
    (w.eval_mem_relativeSeries _ h (Subgroup.subset_normalClosure hh) x)

theorem subgroupTerminalMultihom_closure {α : Type*} [DecidableEq α]
    {G : Type*} [Group G] (H : Subgroup G)
    (l : List α) (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    (hnext : relativeSeries (Subgroup.normalClosure (H : Set G)) (l.length+1) = ⊥) :
    Subgroup.closure (Set.range (subgroupTerminalMultihom H (leftList l)
      (by simpa using hl) (by simpa using hall) (by simpa using hnext))) =
      relativeSeries (Subgroup.normalClosure (H : Set G)) l.length := by
  rw [subgroupTerminalMultihom_range]
  exact closure_leftList_values (H : Set G) l hl hnext

end MarkedCommutatorWord
end DirectedCycles
