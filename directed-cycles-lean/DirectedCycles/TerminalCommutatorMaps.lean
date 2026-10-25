module

public import DirectedCycles.MarkedVariableMultilinearity

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

namespace CommutatorWord

def terminalMultihom {α : Type*} [DecidableEq α] {G : Type*} [Group G]
    (w : CommutatorWord α) (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : lowerSeries G w.weight = ⊥) : GroupMultihom (fun _ : α => G) G where
  toFun x := w.eval x
  map_one x i := w.eval_update_one_of_mem x i (hall i)
  map_mul x i u v := by
    let q := QuotientGroup.mk' (lowerSeries G w.weight)
    have hi : Function.Injective q := q.ker_eq_bot_iff.mp (by rw [QuotientGroup.ker_mk',hnext])
    apply hi
    rw [_root_.map_mul]
    exact w.eval_mul_mod_next hw x i (hall i) u v

end CommutatorWord
namespace MarkedCommutatorWord

/-- The marked input ranges over N; the ordinary inputs range over G. -/
abbrev Input {G : Type*} [Group G] (N : Subgroup G) (α : Type*) : Option α → Type _
  | none => N
  | some _ => G

instance inputGroup {G : Type*} [Group G] (N : Subgroup G) (α : Type*) (i : Option α) :
    Group (Input N α i) := by cases i <;> infer_instance

/-- A terminal relative commutator form is an actual separately homomorphic
map. The vanishing hypothesis is a central-series equality, not an assumed
multilinearity law. -/
def terminalMultihom {α : Type*} [DecidableEq α] {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries N (w.degree+1) = ⊥) : GroupMultihom (Input N α) G where
  toFun x := w.eval (x none).val (fun i => x (some i))
  map_one x i := by
    cases i with
    | none =>
      simpa only [Function.update_self,Function.update_of_ne (Option.some_ne_none _),Subgroup.coe_one]
        using w.eval_one_marked (fun i => x (some i))
    | some i =>
      have he : (fun j => Function.update x (some i) 1 (some j)) =
          Function.update (fun j => x (some j)) i 1 := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji]
      rw [Function.update_of_ne (by simp : (none : Option α) ≠ some i),he]
      exact w.eval_update_one_of_mem (x none).val (fun i => x (some i)) i (hall i)
  map_mul x i u v := by
    let q := QuotientGroup.mk' (relativeSeries N (w.degree+1))
    have hq : Function.Injective q := q.ker_eq_bot_iff.mp (by rw [QuotientGroup.ker_mk',hnext])
    apply hq
    rw [_root_.map_mul]
    cases i with
    | none =>
      simpa only [Function.update_self,Function.update_of_ne (Option.some_ne_none _),Subgroup.coe_mul]
        using w.eval_mul_marked_mod_next N (fun i => x (some i)) u.val v.val u.property v.property
    | some i =>
      have he : ∀ z : G, (fun j => Function.update x (some i) z (some j)) =
          Function.update (fun j => x (some j)) i z := by
        intro z
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji]
      simp only [Function.update_of_ne (by simp : (none : Option α) ≠ some i),he]
      exact w.eval_mul_variable_mod_next N hw (x none).val (x none).property (fun i => x (some i))
        i (hall i) u v

end MarkedCommutatorWord
end DirectedCycles
