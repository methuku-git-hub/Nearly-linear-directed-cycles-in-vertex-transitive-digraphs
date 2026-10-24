import DirectedCycles.Basic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace DirectedCycles

/-- Half-open expansion positions at one quotient vertex. The fixed run omits
its final retained point, which is the zero-th outgoing connector point. -/
inductive ExpansionBand (l D : ℕ) where
  | fixed : Fin l → ExpansionBand l D
  | outgoing : Fin (D+1) → ExpansionBand l D
  | incoming : Fin D → ExpansionBand l D
  deriving DecidableEq

/-- Incoming index q denotes q+1 backwards steps from the next retained start. -/
def ExpansionBand.coordinate {l D : ℕ} (h : ℕ) : ExpansionBand l D → ℕ
  | .fixed k => k.val
  | .outgoing k => l+k.val
  | .incoming k => h-(k.val+1)

theorem ExpansionBand.coordinate_lt {l D h : ℕ} (hgap : l+2*D+2 ≤ h)
    (z : ExpansionBand l D) : z.coordinate h < h := by
  cases z with
  | fixed k => dsimp [coordinate]; have := k.isLt; omega
  | outgoing k => dsimp [coordinate]; have := k.isLt; omega
  | incoming k => dsimp [coordinate]; have := k.isLt; omega

/-- The three intervals are pairwise disjoint, including both boundaries. -/
theorem ExpansionBand.coordinate_injective {l D h : ℕ} (hgap : l+2*D+2 ≤ h) :
    Function.Injective (ExpansionBand.coordinate (l := l) (D := D) h) := by
  intro x y he
  cases x <;> cases y <;> simp only [coordinate] at he
  all_goals first
    | congr 1; apply Fin.ext; omega
    | (rename_i i j; have hi := i.isLt; have hj := j.isLt; omega)

/-- An a-step between occupied bands is either a consecutive step within a
band, the last fixed step into its outgoing start, or the final incoming step
into the first fixed point. The numerical gap excludes all other transitions. -/
theorem ExpansionBand.successor_cases {l D h : ℕ}
    (hl : 0 < l) (hgap : l+2*D+2 ≤ h) (x y : ExpansionBand l D)
    (he : (x.coordinate h+1)%h = y.coordinate h) :
    (∃ i j, x = .fixed i ∧ y = .fixed j ∧ i.val+1 = j.val) ∨
    (∃ i, x = .fixed i ∧ y = .outgoing ⟨0,by omega⟩ ∧ i.val+1 = l) ∨
    (∃ i j, x = .outgoing i ∧ y = .outgoing j ∧ i.val+1 = j.val) ∨
    (∃ i j, x = .incoming i ∧ y = .incoming j ∧ j.val+1 = i.val) ∨
    (∃ i, x = .incoming i ∧ y = .fixed ⟨0,hl⟩ ∧ i.val = 0) := by
  have hx := x.coordinate_lt hgap
  have hy := y.coordinate_lt hgap
  have he' : x.coordinate h+1 = y.coordinate h ∨
      x.coordinate h+1 = h ∧ y.coordinate h = 0 := by
    by_cases hh : x.coordinate h+1 < h
    · left; simpa only [Nat.mod_eq_of_lt hh] using he
    · right
      have hh' : x.coordinate h+1 = h := by omega
      rw [hh',Nat.mod_self] at he
      exact ⟨hh',he.symm⟩
  cases x with
  | fixed i =>
    cases y with
    | fixed j =>
      left
      exact ⟨i,j,rfl,rfl,by dsimp [coordinate] at he'; have := i.isLt; omega⟩
    | outgoing j =>
      right; left
      have hi := i.isLt
      have hj := j.isLt
      dsimp [coordinate] at he'
      have hj0 : j = ⟨0,by omega⟩ := Fin.ext (by change j.val = 0; omega)
      exact ⟨i,rfl,congrArg ExpansionBand.outgoing hj0,by omega⟩
    | incoming j => dsimp [coordinate] at he'; have := i.isLt; have := j.isLt; omega
  | outgoing i =>
    cases y with
    | fixed j => dsimp [coordinate] at he'; have := i.isLt; have := j.isLt; omega
    | outgoing j =>
      right; right; left
      exact ⟨i,j,rfl,rfl,by dsimp [coordinate] at he'; have := i.isLt; have := j.isLt; omega⟩
    | incoming j => dsimp [coordinate] at he'; have := i.isLt; have := j.isLt; omega
  | incoming i =>
    cases y with
    | fixed j =>
      right; right; right; right
      have hi := i.isLt
      have hj := j.isLt
      dsimp [coordinate] at he'
      have hj0 : j = ⟨0,hl⟩ := Fin.ext (by change j.val = 0; omega)
      exact ⟨i,rfl,congrArg ExpansionBand.fixed hj0,by omega⟩
    | outgoing j => dsimp [coordinate] at he'; have := i.isLt; have := j.isLt; omega
    | incoming j =>
      right; right; right; left
      exact ⟨i,j,rfl,rfl,by dsimp [coordinate] at he'; have := i.isLt; have := j.isLt; omega⟩

end DirectedCycles
