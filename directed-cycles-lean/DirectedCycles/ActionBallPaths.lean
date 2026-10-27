module

public import DirectedCycles.ActionBalls
public import DirectedCycles.BoundedWalks

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

theorem relationBall_mono {V : Type*} (R : Digraph V) (e : V) :
    Monotone (relationBall R e) := by
  intro n m h
  induction h with
  | refl => exact Set.Subset.refl _
  | @step m _ ih => exact ih.trans (relationBall_step R e m)

theorem relationBall_iff_reachWithin {V : Type*} (R : Digraph V) (e y : V) (n : ℕ) :
    y ∈ relationBall R e n ↔ ReachWithin R n e y := by
  constructor
  · intro h
    induction n generalizing y with
    | zero =>
      have he : y = e := h
      subst y
      exact ReachWithin.refl e 0
    | succ n ih =>
      obtain ⟨x,hx,he | he⟩ := h
      · subst y
        exact (ih x hx).mono (by omega)
      · exact (ih x hx).trans (ReachWithin.arc he)
  · rintro ⟨W,hW⟩
    have hw : y ∈ relationBall R e W.length := by
      clear hW
      induction W with
      | nil => rfl
      | @cons y z W hyz ih => exact ⟨y,ih,Or.inr hyz⟩
    exact relationBall_mono R e hW hw

theorem relationBall_card_bounds {V : Type*} [Finite V] (R : Digraph V) (e : V) (n : ℕ) :
    1 ≤ Nat.card (relationBall R e n) ∧ Nat.card (relationBall R e n) ≤ Nat.card V := by
  have he : e ∈ relationBall R e n := (relationBall_iff_reachWithin R e e n).mpr (ReachWithin.refl e n)
  let : Nonempty (relationBall R e n) := ⟨⟨e,he⟩⟩
  exact ⟨Nat.card_pos,Nat.card_le_card_of_injective Subtype.val Subtype.val_injective⟩

/-- A normal subgroup inside a step-set power has short paths within all
of its orbits, not merely at the chosen base vertex. -/
theorem normal_subgroup_ball_short_paths {G V : Type*} [Group G] [MulAction G V]
    (R : Digraph V) (e : V) (hR : ∀ g : G, ∀ x y, R (g • x) (g • y) ↔ R x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (H : Subgroup G) [H.Normal]
    (k : ℕ) (hk : 1 ≤ k) (hH : (H : Set G) ⊆ actionStepSet R e ^ k) :
    ∀ x y : V, MulAction.orbitRel H V x y → ∃ P : SimplePath R x y, P.length ≤ k := by
  intro x y hxy
  obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hxy
  have hy : h⁻¹ • x = y := by rw [← hh,inv_smul_smul]
  obtain ⟨t,htex⟩ := ht e x
  have hc : t⁻¹*(h⁻¹ : H).val*t ∈ H := by
    simpa only [inv_inv] using (inferInstance : H.Normal).conj_mem (h⁻¹ : H).val (h⁻¹ : H).property t⁻¹
  have hb := hH hc
  rw [actionStepSet_pow R e hR ht k hk] at hb
  have hp := (relationBall_iff_reachWithin R e _ k).mp hb
  have hmap := hp.map (fun z => t • z) (fun u v huv => (hR t u v).mpr huv)
  have he : t • ((t⁻¹*(h⁻¹ : H).val*t) • e) = y := by
    rw [mul_smul,mul_smul,smul_inv_smul,htex]
    exact hy
  rw [htex,he] at hmap
  exact reachWithin_iff_simplePath.mp hmap

end DirectedCycles
