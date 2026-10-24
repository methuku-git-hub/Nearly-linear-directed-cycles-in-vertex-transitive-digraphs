import Mathlib.Combinatorics.Additive.ApproximateSubgroup
import Mathlib.Tactic

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G] [DecidableEq G]

def rightTranslate (B : Finset G) (g : G) : Finset G := B.image (fun b => b*g)

@[simp] theorem mem_rightTranslate (B : Finset G) (g x : G) :
    x ∈ rightTranslate B g ↔ x*g⁻¹ ∈ B := by
  simp only [rightTranslate,Finset.mem_image]
  constructor
  · rintro ⟨b,hb,rfl⟩
    simpa using hb
  · intro h
    exact ⟨x*g⁻¹,h,by simp⟩

@[simp] theorem rightTranslate_one (B : Finset G) : rightTranslate B 1 = B := by
  ext x
  simp

@[simp] theorem rightTranslate_mul (B : Finset G) (g h : G) :
    rightTranslate B (g*h) = rightTranslate (rightTranslate B g) h := by
  ext x
  simp [mul_assoc]

@[simp] theorem card_rightTranslate (B : Finset G) (g : G) :
    (rightTranslate B g).card = B.card :=
  Finset.card_image_of_injective _ (mul_left_injective g)

@[simp] theorem rightTranslate_sdiff (B C : Finset G) (g : G) :
    rightTranslate (B\C) g = rightTranslate B g \ rightTranslate C g := by
  ext x
  simp

@[simp] theorem rightTranslate_inter (B C : Finset G) (g : G) :
    rightTranslate (B ∩ C) g = rightTranslate B g ∩ rightTranslate C g := by
  ext x
  simp

def defect (B : Finset G) (g : G) : ℕ := (B \ rightTranslate B g).card

@[simp] theorem defect_one (B : Finset G) : defect B 1 = 0 := by simp [defect]

theorem defect_mul_le (B : Finset G) (g h : G) :
    defect B (g*h) ≤ defect B g + defect B h := by
  have hs : B \ rightTranslate B (g*h) ⊆
      (B \ rightTranslate B h) ∪
      (rightTranslate B h \ rightTranslate (rightTranslate B g) h) := by
    intro x hx
    simp only [Finset.mem_sdiff,Finset.mem_union,rightTranslate_mul] at *
    by_cases hx' : x ∈ rightTranslate B h
    · exact Or.inr ⟨hx',hx.2⟩
    · exact Or.inl ⟨hx.1,hx'⟩
  calc
    defect B (g*h) ≤ ((B \ rightTranslate B h) ∪
      (rightTranslate B h \ rightTranslate (rightTranslate B g) h)).card := Finset.card_le_card hs
    _ ≤ (B \ rightTranslate B h).card +
      (rightTranslate B h \ rightTranslate (rightTranslate B g) h).card := Finset.card_union_le _ _
    _ = defect B g + defect B h := by
      rw [← rightTranslate_sdiff,card_rightTranslate]
      exact Nat.add_comm _ _

theorem defect_add_overlap (B : Finset G) (g : G) :
    defect B g + (B ∩ rightTranslate B g).card = B.card :=
  Finset.card_sdiff_add_card_inter _ _

@[simp] theorem defect_inv (B : Finset G) (g : G) : defect B g⁻¹ = defect B g := by
  have he : (B ∩ rightTranslate B g⁻¹).card = (B ∩ rightTranslate B g).card := by
    rw [← card_rightTranslate (B ∩ rightTranslate B g⁻¹) g,rightTranslate_inter]
    simp only [← rightTranslate_mul,inv_mul_cancel,rightTranslate_one]
    rw [Finset.inter_comm]
  have h1 := defect_add_overlap B g⁻¹
  have h2 := defect_add_overlap B g
  omega

/-- Errors add along a word; all quantities here are actual finite-set counts. -/
theorem defect_le_of_mem_pow (B : Finset G) (S : Set G) (ε : ℝ)
    (hS : ∀ g ∈ S, (defect B g : ℝ) ≤ ε) (n : ℕ) :
    ∀ g ∈ S^n, (defect B g : ℝ) ≤ n*ε := by
  induction n with
  | zero =>
    intro g hg
    have : g = 1 := by simpa using hg
    simp [this]
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    obtain ⟨x,hx,y,hy,rfl⟩ := hg
    have hc : (defect B (x*y) : ℝ) ≤ defect B x + defect B y := by
      exact_mod_cast defect_mul_le B x y
    have hn := ih x hx
    have hy' := hS y hy
    push_cast
    nlinarith

/-- A translate with error smaller than the set meets the original set,
so its translating element lies in the corresponding difference set. -/
theorem mem_difference_of_defect_lt (B : Finset G) (g : G)
    (h : defect B g < B.card) : g ∈ (B : Set G)⁻¹ * (B : Set G) := by
  have ho : 0 < (B ∩ rightTranslate B g).card := by
    have := defect_add_overlap B g
    omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp ho
  obtain ⟨hxB,hxg⟩ := Finset.mem_inter.mp hx
  obtain ⟨b,hb,hbg⟩ := Finset.mem_image.mp hxg
  exact ⟨b⁻¹,by simpa using hb,x,hxB,by rw [← hbg]; simp⟩

theorem pow_subset_difference (B : Finset G) (S : Set G) (ε : ℝ) (n : ℕ)
    (hS : ∀ g ∈ S, (defect B g : ℝ) ≤ ε) (hn : n*ε < B.card) :
    S^n ⊆ (B : Set G)⁻¹ * (B : Set G) := by
  intro g hg
  apply mem_difference_of_defect_lt B g
  have := (defect_le_of_mem_pow B S ε hS n g hg).trans_lt hn
  exact_mod_cast this

end FiniteAlmostPeriods
end DirectedCycles
