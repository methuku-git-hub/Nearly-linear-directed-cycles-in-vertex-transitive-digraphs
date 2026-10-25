module

public import DirectedCycles.BoundedDifferenceConstraints
public import DirectedCycles.RunResidues

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Simultaneous residue choices with the manuscript's exact run bounds
and its incident collision-constraint budget. The constraints may repeat
pairs of variables, as happens for a two-vertex quotient cycle. -/
theorem choose_separated_run_residues {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I]
    (h q D : ℕ) [NeZero h] (hh : 8*(q+1)*(D+1) < h)
    (σ : Equiv.Perm I) (hσ : ∀ i, σ i ≠ i) (ν : I → ZMod h)
    (src dst : C → I) (bad : C → Finset (ZMod h))
    (hne : ∀ c, src c ≠ dst c) (hcard : ∀ c, (bad c).card ≤ 2*D+1)
    (hdegree : ∀ i, (Finset.univ.filter (fun c => src c = i ∨ dst c = i)).card ≤ 2*q) :
    ∃ v : I → ZMod h,
      (∀ i, (h+7)/8 ≤ (v i-v (σ i)-((D : ZMod h)+ν i)).val ∧
        (v i-v (σ i)-((D : ZMod h)+ν i)).val ≤ h-2*D-2) ∧
      (∀ c, v (dst c)-v (src c) ∉ bad c) := by
  classical
  have hb := separated_run_lower h q D hh
  let runBad := fun i => (badRunResidues h D).image (fun l => l+((D : ZMod h)+ν i))
  have hrc : ∀ i, (runBad i).card ≤ (h+7)/8+2*D+1 := by
    intro i
    exact Finset.card_image_le.trans (badRunResidues_card h D (by omega))
  obtain ⟨v,hr,hc⟩ := two_family_difference_assignment σ id src dst runBad bad
    2 (2*q) ((h+7)/8+2*D+1) (2*D+1) hσ hne hrc hcard
    (permutation_incident_card_le_two σ) hdegree (by
      simpa only [ZMod.card] using separated_run_forbidden_budget h q D hh)
  refine ⟨v,?_,hc⟩
  intro i
  apply run_bounds_of_not_bad h D hb.2
  intro he
  apply hr i
  exact Finset.mem_image.mpr ⟨v i-v (σ i)-((D : ZMod h)+ν i),he,sub_add_cancel _ _⟩

/-- A common translation normalizes the initial run without changing
any difference constraint or run length. -/
theorem normalize_run_residues {I A : Type*} [AddCommGroup A]
    (σ : Equiv.Perm I) (v ν : I → A) (d : A) (i₀ : I) :
    ∃ w : I → A, w (σ i₀)+d+ν i₀ = 0 ∧
      ∀ i j, w i-w j = v i-v j := by
  refine ⟨fun i => v i-(v (σ i₀)+d+ν i₀),?_,?_⟩
  · dsimp only
    abel
  · intro i j
    dsimp only
    abel

theorem residue_run_closure {I : Type*} [Fintype I] (h D : ℕ) [NeZero h]
    (σ : Equiv.Perm I) (v ν : I → ZMod h) :
    (∑ i, ((((v i-v (σ i)-((D : ZMod h)+ν i)).val : ℕ) : ZMod h)+(D : ZMod h))) +
      ∑ i, ν i = 0 := by
  have he : ∀ i, (((v i-v (σ i)-((D : ZMod h)+ν i)).val : ℕ) : ZMod h) +
      (D : ZMod h) + ν i = v i-v (σ i) := by
    intro i
    rw [ZMod.natCast_zmod_val]
    abel
  rw [← Finset.sum_add_distrib]
  simp only [he,Finset.sum_sub_distrib]
  rw [Equiv.sum_comp σ]
  exact sub_self _

end DirectedCycles
