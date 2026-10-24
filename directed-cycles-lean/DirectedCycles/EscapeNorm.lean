import Mathlib.Tactic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The reciprocal lengths of initial power segments staying in a set. -/
def escapeValues (A : Set G) (g : G) : Set ℝ :=
  {x | ∃ n : ℕ, (∀ i ≤ n, g^i ∈ A) ∧ x = 1 / ((n : ℝ)+1)}

/-- BGT's escape norm; all its uses below assume that the set contains one. -/
noncomputable def escapeNorm (A : Set G) (g : G) : ℝ := sInf (escapeValues A g)

theorem escapeValues_nonempty {A : Set G} (hA : 1 ∈ A) (g : G) :
    (escapeValues A g).Nonempty := by
  refine ⟨1, 0, ?_, by norm_num⟩
  intro i hi
  have : i = 0 := by omega
  simpa [this] using hA

theorem escapeValues_bddBelow (A : Set G) (g : G) : BddBelow (escapeValues A g) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, _, rfl⟩
  positivity

theorem escapeNorm_nonneg {A : Set G} (hA : 1 ∈ A) (g : G) : 0 ≤ escapeNorm A g := by
  apply le_csInf (escapeValues_nonempty hA g)
  rintro x ⟨n, _, rfl⟩
  positivity

theorem escapeNorm_le_of_powers {A : Set G} {g : G} {n : ℕ}
    (h : ∀ i ≤ n, g^i ∈ A) : escapeNorm A g ≤ 1 / ((n : ℝ)+1) :=
  csInf_le (escapeValues_bddBelow A g) ⟨n, h, rfl⟩

theorem escapeNorm_le_one {A : Set G} (hA : 1 ∈ A) (g : G) : escapeNorm A g ≤ 1 := by
  apply csInf_le (escapeValues_bddBelow A g)
  exact ⟨0, by simpa using hA, by norm_num⟩

theorem inv_le_escapeNorm_of_not_mem {A : Set G} (hA : 1 ∈ A) {g : G} {n : ℕ}
    (hn : g^n ∉ A) : 1 / (n : ℝ) ≤ escapeNorm A g := by
  apply le_csInf (escapeValues_nonempty hA g)
  rintro x ⟨m, hm, rfl⟩
  have hmn : m < n := by
    by_contra h
    exact hn (hm n (by omega))
  apply one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ)+1)
  exact_mod_cast hmn

theorem escapeNorm_eq_one_of_not_mem {A : Set G} (hA : 1 ∈ A) {g : G}
    (hg : g ∉ A) : escapeNorm A g = 1 := by
  apply le_antisymm (escapeNorm_le_one hA g)
  simpa using inv_le_escapeNorm_of_not_mem hA (n := 1) (by simpa using hg)

theorem mem_of_escapeNorm_lt_one {A : Set G} (hA : 1 ∈ A) {g : G}
    (hg : escapeNorm A g < 1) : g ∈ A := by
  by_contra h
  rw [escapeNorm_eq_one_of_not_mem hA h] at hg
  exact lt_irrefl _ hg

theorem escapeNorm_eq_inv_of_first_exit {A : Set G} (hA : 1 ∈ A) {g : G} {n : ℕ}
    (hn : g^n ∉ A) (hprev : ∀ i < n, g^i ∈ A) :
    escapeNorm A g = 1 / (n : ℝ) := by
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    exact hn (by simpa [this] using hA)
  apply le_antisymm _ (inv_le_escapeNorm_of_not_mem hA hn)
  have h := escapeNorm_le_of_powers (g := g) (n := n-1)
    (fun i hi => hprev i (by omega))
  have hncast : ((n-1 : ℕ) : ℝ)+1 = n := by exact_mod_cast (Nat.sub_add_cancel hn0)
  simpa only [hncast] using h

theorem escapeNorm_eq_zero_iff {A : Set G} (hA : 1 ∈ A) (g : G) :
    escapeNorm A g = 0 ↔ ∀ n : ℕ, g^n ∈ A := by
  constructor
  · intro he n
    by_contra hn
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      exact hn (by simpa [this] using hA)
    have h := inv_le_escapeNorm_of_not_mem hA hn
    rw [he] at h
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  · intro hall
    apply le_antisymm _ (escapeNorm_nonneg hA g)
    by_contra h
    have he : 0 < escapeNorm A g := lt_of_not_ge h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt he
    exact (not_lt_of_ge (escapeNorm_le_of_powers (n := n) (fun i _ => hall i))) hn

theorem escapeNorm_one {A : Set G} (hA : 1 ∈ A) : escapeNorm A (1 : G) = 0 := by
  apply (escapeNorm_eq_zero_iff hA 1).2
  simpa using hA

theorem escapeNorm_inv {A : Set G} (hA : A⁻¹ = A) (g : G) :
    escapeNorm A g⁻¹ = escapeNorm A g := by
  unfold escapeNorm
  congr 1
  ext x
  constructor <;> rintro ⟨n, hn, rfl⟩ <;> refine ⟨n, ?_, rfl⟩ <;> intro i hi
  · have h := hn i hi
    have hm : ((g⁻¹)^i)⁻¹ ∈ A⁻¹ := Set.inv_mem_inv.mpr h
    simpa [hA] using hm
  · have h := hn i hi
    have hm : (g^i)⁻¹ ∈ A⁻¹ := Set.inv_mem_inv.mpr h
    simpa [hA] using hm

theorem escapeNorm_antitone {A B : Set G} (hA : 1 ∈ A) (hAB : A ⊆ B) (g : G) :
    escapeNorm B g ≤ escapeNorm A g := by
  apply le_csInf (escapeValues_nonempty hA g)
  rintro x ⟨n, hn, rfl⟩
  exact escapeNorm_le_of_powers (fun i hi => hAB (hn i hi))
end DirectedCycles
