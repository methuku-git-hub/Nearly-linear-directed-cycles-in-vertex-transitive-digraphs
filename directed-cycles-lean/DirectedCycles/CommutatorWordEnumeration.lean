import DirectedCycles.CommutatorWords
import Mathlib.Data.Finset.NAry

set_option autoImplicit false
namespace DirectedCycles

namespace CommutatorWord
variable {α : Type*} [Fintype α]

noncomputable def enumerate : ℕ → Finset (CommutatorWord α)
  | 0 => by classical exact Finset.univ.image .var
  | n+1 => by classical exact Finset.univ.image .var ∪ Finset.image₂ .bracket (enumerate n) (enumerate n)

theorem mem_enumerate_of_weight_le (n : ℕ) (w : CommutatorWord α) (hw : w.weight ≤ n+1) :
    w ∈ enumerate n := by
  classical
  induction n generalizing w with
  | zero =>
    cases w with
    | var i => exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    | bracket a b =>
      have ha := a.weight_pos
      have hb := b.weight_pos
      change a.weight+b.weight ≤ 0+1 at hw
      omega
  | succ n ih =>
    cases w with
    | var i => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    | bracket a b =>
      have ha := a.weight_pos
      have hb := b.weight_pos
      change a.weight+b.weight ≤ n+1+1 at hw
      exact Finset.mem_union_right _ (Finset.mem_image₂.mpr ⟨a,ih a (by omega),b,ih b (by omega),rfl⟩)

def countBound (k : ℕ) : ℕ → ℕ
  | 0 => k
  | n+1 => k+(countBound k n)^2

theorem enumerate_card_le (n : ℕ) : (enumerate (α := α) n).card ≤ countBound (Fintype.card α) n := by
  classical
  induction n with
  | zero => exact Finset.card_image_le.trans_eq (Finset.card_univ)
  | succ n ih =>
    have h1 := Finset.card_union_le (Finset.univ.image (var : α → CommutatorWord α))
      (Finset.image₂ bracket (enumerate n) (enumerate n))
    have h2 := Finset.card_image₂_le bracket (enumerate (α := α) n) (enumerate n)
    have h3 : (Finset.univ.image (var : α → CommutatorWord α)).card ≤ Fintype.card α :=
      Finset.card_image_le.trans_eq Finset.card_univ
    change (Finset.univ.image var ∪ Finset.image₂ bracket (enumerate n) (enumerate n)).card ≤ _
    change _ ≤ Fintype.card α+(countBound (Fintype.card α) n)^2
    nlinarith

end CommutatorWord

namespace MarkedCommutatorWord
variable {α : Type*} [Fintype α]

noncomputable def enumerate : ℕ → Finset (MarkedCommutatorWord α)
  | 0 => {marked}
  | n+1 => by
    classical
    exact {marked} ∪
      Finset.image₂ MarkedCommutatorWord.left (enumerate n) (CommutatorWord.enumerate n) ∪
      Finset.image₂ MarkedCommutatorWord.right (CommutatorWord.enumerate n) (enumerate n)

theorem mem_enumerate_of_degree_le (n : ℕ) (w : MarkedCommutatorWord α) (hw : w.degree ≤ n) :
    w ∈ enumerate n := by
  classical
  induction n generalizing w with
  | zero =>
    cases w with
    | marked => exact Finset.mem_singleton_self _
    | left a b =>
      have hb := b.weight_pos
      change a.degree+b.weight ≤ 0 at hw
      omega
    | right a b =>
      have ha := a.weight_pos
      change a.weight+b.degree ≤ 0 at hw
      omega
  | succ n ih =>
    cases w with
    | marked => exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    | left a b =>
      have hb := b.weight_pos
      change a.degree+b.weight ≤ n+1 at hw
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image₂.mpr
        ⟨a,ih a (by omega),b,CommutatorWord.mem_enumerate_of_weight_le n b (by omega),rfl⟩))
    | right a b =>
      have ha := a.weight_pos
      change a.weight+b.degree ≤ n+1 at hw
      exact Finset.mem_union_right _ (Finset.mem_image₂.mpr
        ⟨a,CommutatorWord.mem_enumerate_of_weight_le n a (by omega),b,ih b (by omega),rfl⟩)

def countBound (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => 1+2*countBound k n*CommutatorWord.countBound k n

theorem enumerate_card_le (n : ℕ) : (enumerate (α := α) n).card ≤ countBound (Fintype.card α) n := by
  classical
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hc := CommutatorWord.enumerate_card_le (α := α) n
    have h1 := Finset.card_union_le ({marked} ∪ Finset.image₂ MarkedCommutatorWord.left (enumerate (α := α) n) (CommutatorWord.enumerate n))
      (Finset.image₂ MarkedCommutatorWord.right (CommutatorWord.enumerate n) (enumerate n))
    have h2 := Finset.card_union_le {marked} (Finset.image₂ MarkedCommutatorWord.left (enumerate (α := α) n) (CommutatorWord.enumerate n))
    have h3 := Finset.card_image₂_le MarkedCommutatorWord.left (enumerate (α := α) n) (CommutatorWord.enumerate n)
    have h4 := Finset.card_image₂_le MarkedCommutatorWord.right (CommutatorWord.enumerate n) (enumerate (α := α) n)
    simp only [Finset.card_singleton] at h2
    have hm := Nat.mul_le_mul ih hc
    change ({marked} ∪ Finset.image₂ MarkedCommutatorWord.left (enumerate (α := α) n) (CommutatorWord.enumerate n) ∪
      Finset.image₂ MarkedCommutatorWord.right (CommutatorWord.enumerate n) (enumerate n)).card ≤ _
    change _ ≤ 1+2*countBound (Fintype.card α) n*CommutatorWord.countBound (Fintype.card α) n
    nlinarith

end MarkedCommutatorWord
end DirectedCycles
