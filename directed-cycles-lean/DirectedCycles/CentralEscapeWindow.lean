module

public import DirectedCycles.EscapeSublevelPowers
public import DirectedCycles.ShortPowerProgression
public import DirectedCycles.LocalQuotientCancellation

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- A small escape window in the centralizer of the chosen element. -/
def centralEscapeWindow (A : Set G) (u : G) (r : ℝ) : Set G :=
  escapeSublevel A r ∩ {x | Commute x u}

theorem one_mem_centralEscapeWindow {A : Set G} (hA : 1 ∈ A) (u : G)
    {r : ℝ} (hr : 0 ≤ r) : (1 : G) ∈ centralEscapeWindow A u r :=
  ⟨one_mem_escapeSublevel hA hr,Commute.one_left u⟩

theorem centralEscapeWindow_symmetric {A : Set G} (hi : A⁻¹ = A) (u : G) (r : ℝ) :
    (centralEscapeWindow A u r)⁻¹ = centralEscapeWindow A u r := by
  ext x
  simp only [Set.mem_inv,centralEscapeWindow,Set.mem_inter_iff,escapeSublevel,
    Set.mem_ofPred_eq,escapeNorm_inv hi]
  constructor
  · rintro ⟨hx,hc⟩
    exact ⟨hx,by simpa using hc.inv_left⟩
  · rintro ⟨hx,hc⟩
    exact ⟨hx,hc.inv_left⟩

theorem centralEscapeWindow_power_subset {A : Set G} {P : ℝ} (hP : 0 ≤ P)
    (hprod : ∀ l : List G, escapeNorm A l.prod ≤ P*(l.map (escapeNorm A)).sum)
    (u : G) (r : ℝ) (n : ℕ) :
    (centralEscapeWindow A u r)^n ⊆ centralEscapeWindow A u (P*n*r) := by
  intro x hx
  refine ⟨escapeSublevel_power_subset hP hprod r n
    ((Set.pow_subset_pow_left (fun _ hy => hy.1)) hx),?_⟩
  induction n generalizing x with
  | zero =>
    have hx1 : x = 1 := by simpa using hx
    subst x
    exact Commute.one_left u
  | succ n ih =>
    rw [pow_succ] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hx
    exact (ih ha).mul_left hb.2

/-- The first-exit progression can be quotiented on an explicitly constructed
symmetric escape window. This does not assert that the window is large or that
a Lie dimension drops; those are separate obligations. -/
theorem exists_shortProgression_quotient_window {A : Set G} (hA : 1 ∈ A) (hi : A⁻¹ = A)
    (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    {B : ℝ} (hB : 0 < B)
    (hprod : ∀ l : List G, escapeNorm A l.prod ≤ B*(l.map (escapeNorm A)).sum)
    (u : G) {N : ℕ} (hN : 0 < N) (hexit : u^N ∉ A) (hprev : ∀ i < N, u^i ∈ A) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : Set G,
      LocalNormalSet (shortPowerProgression u N) V ∧
      (1 : G) ∈ centralEscapeWindow A u δ ∧
      (centralEscapeWindow A u δ)⁻¹ = centralEscapeWindow A u δ ∧
      (centralEscapeWindow A u δ)^6 ⊆ V := by
  let r : ℝ := 1/(2*((C : ℝ)+2))
  let δ : ℝ := r/(6*B)
  have hr : 0 < r := by dsimp [r]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let V := centralEscapeWindow A u r
  have hV : LocalNormalSet (shortPowerProgression u N) V := by
    apply shortPowerProgression_localNormal hi C htrap u hN hexit hprev
    · intro x hx
      apply powers_mem_of_escapeNorm_small hA
      have hx' : escapeNorm A x ≤ r := hx.1
      have hr' : r < 1/(((C+1 : ℕ) : ℝ)+1) := by
        dsimp [r]
        push_cast
        apply one_div_lt_one_div_of_lt (by positivity)
        linarith
      exact hx'.trans_lt hr'
    · intro x hx
      exact hx.2
  refine ⟨δ,hδ,V,hV,one_mem_centralEscapeWindow hA u hδ.le,
    centralEscapeWindow_symmetric hi u δ,?_⟩
  have he : B*(6 : ℕ)*δ = r := by dsimp [δ]; field_simp
  simpa only [he] using centralEscapeWindow_power_subset hB.le hprod u δ 6
end DirectedCycles
