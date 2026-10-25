module

public import DirectedCycles.BoundedWalks
public import DirectedCycles.GrowthArithmetic
public import DirectedCycles.WeightedExpansion

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

noncomputable def forwardBall {V : Type*} [Fintype V] (D : Digraph V)
    (t : ℕ) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (ReachWithin D t x)

@[simp] theorem mem_forwardBall {V : Type*} [Fintype V] (D : Digraph V)
    (t : ℕ) (x y : V) : y ∈ forwardBall D t x ↔ ReachWithin D t x y := by
  classical
  simp [forwardBall]

theorem forwardBall_mono {V : Type*} [Fintype V] (D : Digraph V)
    (x : V) {s t : ℕ} (hst : s ≤ t) : forwardBall D s x ⊆ forwardBall D t x := by
  intro y hy
  exact (mem_forwardBall D t x y).mpr (((mem_forwardBall D s x y).mp hy).mono hst)

theorem forwardBall_nonempty {V : Type*} [Fintype V] (D : Digraph V)
    (x : V) (t : ℕ) : (forwardBall D t x).Nonempty :=
  ⟨x, (mem_forwardBall D t x x).mpr (ReachWithin.refl x t)⟩

/-- A ball and its external out-boundary are disjoint subsets of the next ball. -/
theorem forwardBall_growth {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) (x : V) (t : ℕ) :
    (forwardBall D t x).card + (outBoundary D (forwardBall D t x)).card ≤
      (forwardBall D (t + 1) x).card := by
  classical
  have hd : Disjoint (forwardBall D t x) (outBoundary D (forwardBall D t x)) := by
    apply Finset.disjoint_left.mpr
    intro y hy hb
    exact ((mem_outBoundary D _ y).mp hb).1 hy
  have hs : forwardBall D t x ∪ outBoundary D (forwardBall D t x) ⊆ forwardBall D (t + 1) x := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact forwardBall_mono D x (by omega) hy
    · obtain ⟨_, z, hz, hzy⟩ := (mem_outBoundary D _ y).mp hy
      exact (mem_forwardBall D (t + 1) x y).mpr
        (((mem_forwardBall D t x z).mp hz).trans (ReachWithin.arc hzy))
  simpa only [Finset.card_union_of_disjoint hd] using Finset.card_le_card hs

/-- The weighted cut bound gives the coarser growth estimate while every
part is at most half occupied. -/
theorem half_fibre_expansion {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (D : Digraph V) (π : V → W)
    (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ : 0 < ρ) (S : Finset V)
    (hhalf : ∀ a, 2 * (S.filter (fun x => π x = a)).card ≤ m)
    (hcut : (∑ a : W, ((S.filter (fun x => π x = a)).card : ℝ) *
      (m - ((S.filter (fun x => π x = a)).card : ℝ))) / (((m : ℝ) - 1) * ρ) ≤
      (outBoundary D S).card) :
    (S.card : ℝ) / (2 * ρ) ≤ (outBoundary D S).card := by
  have hmc : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm' : (0 : ℝ) < m - 1 := by linarith
  have hsum : (∑ a : W, ((S.filter (fun x => π x = a)).card : ℝ)) = S.card := by
    simpa using (Finset.sum_fiberwise S π (fun _ => (1 : ℝ)))
  have hnum : (((m : ℝ) - 1) / 2) * S.card ≤
      ∑ a : W, ((S.filter (fun x => π x = a)).card : ℝ) *
        (m - ((S.filter (fun x => π x = a)).card : ℝ)) := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have ha : (2 : ℝ) * ((S.filter (fun x => π x = a)).card : ℝ) ≤ m := by
      exact_mod_cast hhalf a
    have hn : (0 : ℝ) ≤ (S.filter (fun x => π x = a)).card := Nat.cast_nonneg _
    nlinarith
  calc (S.card : ℝ) / (2 * ρ) =
        ((((m : ℝ) - 1) / 2) * S.card) / (((m : ℝ) - 1) * ρ) := by
          field_simp
       _ ≤ _ := (div_le_div_iff_of_pos_right (mul_pos hm' hρ)).mpr hnum
       _ ≤ _ := hcut

/-- Exponential growth cannot persist until the stated logarithmic time on
a finite graph. Consequently some part is more than half reached. -/
theorem reaches_majority_of_expansion {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (D : Digraph V) (π : V → W)
    (m : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hexpand : ∀ S : Finset V, (∀ a, 2 * (S.filter (fun x => π x = a)).card ≤ m) →
      (S.card : ℝ) / (2 * ρ) ≤ (outBoundary D S).card) (x : V) :
    let u := ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊
    ∃ a, m < 2 * ((forwardBall D u x).filter (fun y => π y = a)).card := by
  classical
  let : Nonempty V := ⟨x⟩
  let u := ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊
  change ∃ a, m < 2 * ((forwardBall D u x).filter (fun y => π y = a)).card
  by_contra! hbad
  have hp : 0 < ρ := by linarith
  have hstep : ∀ j, j < u →
      (forwardBall D j x).card * (1 + 1 / (2 * ρ)) ≤
        ((forwardBall D (j + 1) x).card : ℝ) := by
    intro j hj
    have hhalf : ∀ a, 2 * ((forwardBall D j x).filter (fun y => π y = a)).card ≤ m := by
      intro a
      apply le_trans _ (hbad a)
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      exact Finset.filter_subset_filter _ (forwardBall_mono D x (by omega))
    have he := hexpand (forwardBall D j x) hhalf
    have hg : ((forwardBall D j x).card : ℝ) +
        (outBoundary D (forwardBall D j x)).card ≤ (forwardBall D (j + 1) x).card := by
      exact_mod_cast forwardBall_growth D x j
    have hr : ((forwardBall D j x).card : ℝ) * (1 + 1 / (2 * ρ)) =
        (forwardBall D j x).card + (forwardBall D j x).card / (2 * ρ) := by ring
    rw [hr]
    linarith
  have hpower : ∀ j, j ≤ u → (1 + 1 / (2 * ρ)) ^ j ≤ ((forwardBall D j x).card : ℝ) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [pow_zero]
      exact_mod_cast Finset.card_pos.mpr (forwardBall_nonempty D x 0)
    | succ j ih =>
      intro hj
      rw [pow_succ]
      apply le_trans (mul_le_mul_of_nonneg_right (ih (by omega)) (by positivity))
      exact hstep j (by omega)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hlarge := reachability_growth_ceil hρ hn
  have hsmall : ((forwardBall D u x).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ (forwardBall D u x)
  have hmid := hpower u le_rfl
  change 2 * (Fintype.card V : ℝ) ≤ (1 + 1 / (2 * ρ)) ^ u at hlarge
  linarith

/-- Reachability consequence of Lemma 4.1 with its exact logarithmic radius. -/
theorem directed_reaches_majority {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V]
    (H : Subgroup G) [H.Normal]
    [Fintype (Quotient (MulAction.orbitRel H V))]
    [DecidableEq (Quotient (MulAction.orbitRel H V))]
    (D : Digraph V)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hsize : ∀ a : Quotient (MulAction.orbitRel H V),
      (Finset.univ.filter (fun x => Quotient.mk'' x = a)).card = m)
    (hdiam : ∀ x y, MulAction.orbitRel H V x y →
      ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y, (P.length : ℝ) ≤ ρ)
    (x : V) :
    let u := ⌈4 * ρ * Real.log (2 * (Fintype.card V : ℝ))⌉₊
    ∃ a : Quotient (MulAction.orbitRel H V),
      m < 2 * ((forwardBall D u x).filter (fun y => Quotient.mk'' y = a)).card := by
  apply reaches_majority_of_expansion D
    (fun y => (Quotient.mk'' y : Quotient (MulAction.orbitRel H V))) m ρ hρ
  intro S hhalf
  exact half_fibre_expansion D _ m hm ρ (by linarith) S hhalf
    (directed_weighted_cut H D hD ht m hm ρ hρ hsize hdiam S).1

end DirectedCycles
