module

public import DirectedCycles.LocalGroupProducts
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A power is in A only when its all-bracketings product is defined in the
local group and its value lies in A. -/
def PowerIn (A : Set G) (g : G) (n : ℕ) : Prop :=
  ∃ x ∈ A, L.Product (List.replicate n g) x

theorem powerIn_zero (A : Set G) (g : G) : L.PowerIn A g 0 ↔ L.one ∈ A := by
  constructor
  · rintro ⟨x,hx,hp⟩
    have he := (Product.nil_iff L).1 hp
    simpa only [he] using hx
  · exact fun h => ⟨L.one,h,Product.nil⟩

theorem powerIn_one (A : Set G) (g : G) : L.PowerIn A g 1 ↔ g ∈ A := by
  constructor
  · rintro ⟨x,hx,hp⟩
    have he := (Product.singleton_iff L).1 hp
    simpa only [he] using hx
  · exact fun h => ⟨g,h,Product.singleton g⟩

def escapeValues (A : Set G) (g : G) : Set ℝ :=
  {x | ∃ n : ℕ, (∀ i ≤ n, L.PowerIn A g i) ∧ x = 1/((n : ℝ)+1)}

noncomputable def escapeNorm (A : Set G) (g : G) : ℝ := sInf (L.escapeValues A g)

theorem escapeValues_nonempty {A : Set G} (hA : L.one ∈ A) (g : G) :
    (L.escapeValues A g).Nonempty := by
  refine ⟨1,0,?_,by norm_num⟩
  intro i hi
  have he : i = 0 := by omega
  subst i
  exact (L.powerIn_zero A g).2 hA

theorem escapeValues_bddBelow (A : Set G) (g : G) : BddBelow (L.escapeValues A g) := by
  refine ⟨0,?_⟩
  rintro x ⟨n,_,rfl⟩
  positivity

theorem escapeNorm_nonneg {A : Set G} (hA : L.one ∈ A) (g : G) : 0 ≤ L.escapeNorm A g := by
  apply le_csInf (L.escapeValues_nonempty hA g)
  rintro x ⟨n,_,rfl⟩
  positivity

theorem escapeNorm_le_of_powers {A : Set G} {g : G} {n : ℕ}
    (h : ∀ i ≤ n, L.PowerIn A g i) : L.escapeNorm A g ≤ 1/((n : ℝ)+1) :=
  csInf_le (L.escapeValues_bddBelow A g) ⟨n,h,rfl⟩

theorem escapeNorm_le_one {A : Set G} (hA : L.one ∈ A) (g : G) : L.escapeNorm A g ≤ 1 := by
  have h : ∀ i ≤ 0, L.PowerIn A g i := by
    intro i hi
    have he : i = 0 := by omega
    subst i
    exact (L.powerIn_zero A g).2 hA
  simpa using L.escapeNorm_le_of_powers (g := g) (n := 0) h

theorem inv_le_escapeNorm_of_not_powerIn {A : Set G} (hA : L.one ∈ A) {g : G} {n : ℕ}
    (hn : ¬ L.PowerIn A g n) : 1/(n : ℝ) ≤ L.escapeNorm A g := by
  apply le_csInf (L.escapeValues_nonempty hA g)
  rintro x ⟨m,hm,rfl⟩
  have hmn : m < n := by
    by_contra h
    exact hn (hm n (by omega))
  apply one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ)+1)
  exact_mod_cast hmn

theorem escapeNorm_eq_zero_iff {A : Set G} (hA : L.one ∈ A) (g : G) :
    L.escapeNorm A g = 0 ↔ ∀ n : ℕ, L.PowerIn A g n := by
  constructor
  · intro he n
    by_contra hn
    have hn0 : 0 < n := by
      by_contra h
      have hnz : n = 0 := by omega
      subst n
      exact hn ((L.powerIn_zero A g).2 hA)
    have hh := L.inv_le_escapeNorm_of_not_powerIn hA hn
    rw [he] at hh
    have : 0 < 1/(n : ℝ) := by positivity
    linarith
  · intro hall
    apply le_antisymm _ (L.escapeNorm_nonneg hA g)
    by_contra h
    have he : 0 < L.escapeNorm A g := lt_of_not_ge h
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt he
    exact (not_lt_of_ge (L.escapeNorm_le_of_powers (n := n) (fun i _ => hall i))) hn

theorem escapeNorm_eq_one_of_not_mem {A : Set G} (hA : L.one ∈ A) {g : G}
    (hg : g ∉ A) : L.escapeNorm A g = 1 := by
  apply le_antisymm (L.escapeNorm_le_one hA g)
  simpa using L.inv_le_escapeNorm_of_not_powerIn hA (n := 1) (fun h => hg ((L.powerIn_one A g).1 h))

theorem mem_of_escapeNorm_lt_one {A : Set G} (hA : L.one ∈ A) {g : G}
    (hg : L.escapeNorm A g < 1) : g ∈ A := by
  by_contra h
  rw [L.escapeNorm_eq_one_of_not_mem hA h] at hg
  exact lt_irrefl _ hg
end LocalGroupAlgebra
end DirectedCycles
