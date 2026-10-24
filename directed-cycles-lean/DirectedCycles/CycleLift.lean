import DirectedCycles.Basic
import DirectedCycles.Matching
import Mathlib.Dynamics.PeriodicPts.Lemmas

set_option autoImplicit false

namespace DirectedCycles
open Function

/-- A periodic orbit of an arc-following map is a simple directed cycle. -/
noncomputable def cycleOfPeriod {V : Type*} {D : Digraph V}
    (f : V → V) (x : V) (ha : ∀ v, D v (f v))
    (hp : 2 ≤ minimalPeriod f x) : Cycle D where
  length := minimalPeriod f x
  two_le := hp
  vertex := ⟨fun i => f^[i.val] x, fun i j h => Fin.ext
    ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp h)⟩
  arc i := by
    have hm : 0 < minimalPeriod f x := by omega
    let : NeZero (minimalPeriod f x) := ⟨by omega⟩
    have hnext : f^[((finRotate (minimalPeriod f x) i).val)] x = f (f^[i.val] x) := by
      rw [finRotate_apply]
      have hv : ((i + 1 : Fin (minimalPeriod f x)).val) =
          (i.val + 1) % minimalPeriod f x := by
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < minimalPeriod f x by omega)]
      rw [hv, iterate_mod_minimalPeriod_eq, iterate_succ_apply']
    change D (f^[i.val] x) (f^[(finRotate (minimalPeriod f x) i).val] x)
    rw [hnext]
    exact ha _

/-- A permutation advancing cyclic layers has period at least the number of layers. -/
theorem period_ge_layers {U : Type*} [Finite U] (f : Equiv.Perm U)
    (s : ℕ) (hs : 0 < s) (layer : U → Fin s)
    (hstep : ∀ u, layer (f u) = finRotate s (layer u)) (u : U) :
    s ≤ minimalPeriod f u := by
  let : NeZero s := ⟨by omega⟩
  have hp : 0 < minimalPeriod f u :=
    minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts u)
  have hi : ∀ k, layer (f^[k] u) = (finRotate s)^[k] (layer u) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [iterate_succ_apply', hstep, ih]
  by_contra! hlt
  let k : Fin s := ⟨minimalPeriod f u, hlt⟩
  have he : (finRotate s)^[k.val] (layer u) = layer u := by
    rw [← hi, iterate_minimalPeriod]
  rw [← finCycle_eq_finRotate_iterate, finCycle_apply] at he
  have hk : k = 0 := add_left_cancel (he.trans (add_zero (layer u)).symm)
  have hv := congrArg Fin.val hk
  simp only [k, Fin.val_zero] at hv
  omega

/-- Matchings around a quotient cycle yield a cycle of at least its length.
This is the deterministic lifting step of manuscript Lemma 3.2. -/
theorem cycle_lift_of_fibre_matchings {V W : Type*} [Fintype V]
    {D : Digraph V} {Q : Digraph W} (π : V → W)
    (C : Cycle Q)
    (hne : ∀ i, ∃ x, π x = C.vertex i)
    (hm : ∀ i, ∃ M : {x // π x = C.vertex i} ≃
        {x // π x = C.vertex (finRotate C.length i)}, ∀ x, D x.val (M x).val) :
    ∃ L : Cycle D, C.length ≤ L.length := by
  classical
  choose M hM using hm
  let F : Fin C.length → Type _ := fun i => {x // π x = C.vertex i}
  let U := Σ i, F i
  let f : Equiv.Perm U := Equiv.sigmaCongr (finRotate C.length) M
  let project : U → V := fun u => u.2.val
  have hproject : Injective project := by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hij : i = j := C.vertex.injective (x.property.symm.trans
      ((congrArg π he).trans y.property))
    subst j
    have hxy : x = y := Subtype.ext he
    subst y
    rfl
  let i₀ : Fin C.length := ⟨0, by have := C.two_le; omega⟩
  obtain ⟨x, hx⟩ := hne i₀
  let u : U := ⟨i₀, ⟨x, hx⟩⟩
  have hp : C.length ≤ minimalPeriod f u :=
    period_ge_layers f C.length (by have := C.two_le; omega) Sigma.fst (fun _ => rfl) u
  let E : Digraph U := fun a b => D (project a) (project b)
  have ha : ∀ v, E v (f v) := fun v => hM v.1 v.2
  let L := cycleOfPeriod f u ha (C.two_le.trans hp)
  exact ⟨L.map ⟨project, hproject⟩ (fun _ _ h => h), hp⟩

/-- The restricted action on a fibre fixed setwise by the acting group. -/
@[instance_reducible]
def fibreMulAction {H V W : Type*} [Group H] [MulAction H V]
    (π : V → W) (hπ : ∀ (g : H) x, π (g • x) = π x) (w : W) :
    MulAction H {x // π x = w} where
  smul g x := ⟨g • x.val, (hπ g x.val).trans x.property⟩
  one_smul x := Subtype.ext (one_smul H x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- Manuscript Lemma 3.2 for an orbit partition presented by a surjective map.
The last two hypotheses state exactly that the fibres are group orbits of equal size.
No matching or cycle-existence hypothesis is added. -/
theorem orbit_cycle_lift {H V W : Type*} [Group H] [Fintype V] [MulAction H V]
    (D : Digraph V) (π : V → W) (hs : Surjective π)
    (hπ : ∀ (g : H) x, π (g • x) = π x)
    (hD : ∀ (g : H) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y, π x = π y → ∃ g : H, g • x = y)
    (hc : ∀ a b, Nat.card {x // π x = a} = Nat.card {x // π x = b})
    (C : Cycle (QuotientDigraph D π)) :
    ∃ L : Cycle D, C.length ≤ L.length := by
  classical
  apply cycle_lift_of_fibre_matchings π C (fun i => hs (C.vertex i))
  intro i
  let A := {x // π x = C.vertex i}
  let B := {x // π x = C.vertex (finRotate C.length i)}
  let : MulAction H A := fibreMulAction π hπ _
  let : MulAction H B := fibreMulAction π hπ _
  have ha : ∀ x x' : A, ∃ g : H, g • x = x' := by
    intro x x'
    obtain ⟨g, hg⟩ := ht x.val x'.val (x.property.trans x'.property.symm)
    exact ⟨g, Subtype.ext hg⟩
  have hb : ∀ y y' : B, ∃ g : H, g • y = y' := by
    intro y y'
    obtain ⟨g, hg⟩ := ht y.val y'.val (y.property.trans y'.property.symm)
    exact ⟨g, Subtype.ext hg⟩
  have hcard : Fintype.card A = Fintype.card B := by
    simpa only [A, B, Nat.card_eq_fintype_card] using
      hc (C.vertex i) (C.vertex (finRotate C.length i))
  obtain ⟨_, x, y, hx, hy, hxy⟩ := C.arc i
  have hne : ∃ (a : A) (b : B), D a.val b.val := ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩
  obtain ⟨_, _, _, _, M, hM⟩ := symmetry_matching ha hb hcard
    (fun (a : A) (b : B) => D a.val b.val) hne (fun g a b => hD g a.val b.val)
  exact ⟨M, hM⟩

end DirectedCycles
