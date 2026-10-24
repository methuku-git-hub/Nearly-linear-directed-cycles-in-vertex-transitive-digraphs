import DirectedCycles.EscapeNorm

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Membership in a pointwise power has an actual word of the stated length. -/
theorem exists_list_of_mem_set_power {S : Set G} {n : ℕ} {x : G} (hx : x ∈ S^n) :
    ∃ l : List G, l.length = n ∧ (∀ y ∈ l, y ∈ S) ∧ l.prod = x := by
  induction n generalizing x with
  | zero =>
    have hx1 : x = 1 := by simpa using hx
    subst x
    exact ⟨[],rfl,by simp,rfl⟩
  | succ n ih =>
    rw [pow_succ] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hx
    obtain ⟨l,hl,hs,rfl⟩ := ih ha
    refine ⟨l++[b],by simp [hl],?_,by simp⟩
    intro y hy
    simp only [List.mem_append,List.mem_singleton] at hy
    exact hy.elim (hs y) (fun he => he ▸ hb)

/-- Closed escape sublevels are useful for uniform finite window estimates. -/
def escapeSublevel (A : Set G) (r : ℝ) : Set G := {g | escapeNorm A g ≤ r}

theorem one_mem_escapeSublevel {A : Set G} (hA : 1 ∈ A) {r : ℝ} (hr : 0 ≤ r) :
    (1 : G) ∈ escapeSublevel A r := by simpa [escapeSublevel,escapeNorm_one hA] using hr

theorem escapeSublevel_symmetric {A : Set G} (hi : A⁻¹ = A) (r : ℝ) :
    (escapeSublevel A r)⁻¹ = escapeSublevel A r := by
  ext x
  simp only [Set.mem_inv,escapeSublevel,Set.mem_ofPred_eq,escapeNorm_inv hi]

theorem escapeSublevel_subset {A : Set G} (hA : 1 ∈ A) {r : ℝ} (hr : r < 1) :
    escapeSublevel A r ⊆ A := fun _ hx => mem_of_escapeNorm_lt_one hA (hx.trans_lt hr)

/-- A global product estimate gives uniform control of every finite power of
an escape sublevel; no word-length compactness or transfer axiom is needed. -/
theorem escapeSublevel_power_subset {A : Set G} {P : ℝ} (hP : 0 ≤ P)
    (hprod : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum)
    (r : ℝ) (n : ℕ) : (escapeSublevel A r)^n ⊆ escapeSublevel A (P*n*r) := by
  intro x hx
  obtain ⟨l,hl,hs,rfl⟩ := exists_list_of_mem_set_power hx
  have hsum : (l.map (escapeNorm A)).sum ≤ (l.length : ℝ)*r := by
    clear hl hx
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha : escapeNorm A a ≤ r := hs a (by simp)
      have ht := ih (fun y hy => hs y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith
  change escapeNorm A l.prod ≤ P*n*r
  calc
    escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum := hprod l
    _ ≤ P*((l.length : ℝ)*r) := mul_le_mul_of_nonneg_left hsum hP
    _ = P*n*r := by rw [hl]; ring

/-- A sufficiently small escape sublevel stays in A through all the stated
powers, including the zeroth power. -/
theorem powers_mem_of_escapeNorm_small {A : Set G} (hA : 1 ∈ A) {x : G} {M : ℕ}
    (hx : escapeNorm A x < 1/((M : ℝ)+1)) : ∀ j ≤ M, x^j ∈ A := by
  intro j hj
  by_contra h
  have hj0 : 0 < j := by
    by_contra hz
    have hjz : j = 0 := by omega
    exact h (by simpa [hjz] using hA)
  have hlow := inv_le_escapeNorm_of_not_mem hA h
  have hjr : 0 < (j : ℝ) := by exact_mod_cast hj0
  have hle : 1/((M : ℝ)+1) ≤ 1/(j : ℝ) := by
    apply one_div_le_one_div_of_le hjr
    have : (j : ℝ) ≤ M := by exact_mod_cast hj
    linarith
  exact (not_lt_of_ge (hle.trans hlow)) hx
end DirectedCycles
