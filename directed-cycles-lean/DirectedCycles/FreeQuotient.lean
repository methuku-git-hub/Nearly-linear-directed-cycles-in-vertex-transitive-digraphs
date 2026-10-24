import DirectedCycles.NormalPartitions
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- The subgroup used to remove the stabilizers of a normal action. -/
def stabilizerClosure {G V : Type*} [Group G] [MulAction G V]
    (N : Subgroup G) (x : V) : Subgroup G :=
  Subgroup.normalClosure ((N ⊓ MulAction.stabilizer G x : Subgroup G) : Set G)

instance stabilizerClosure_normal {G V : Type*} [Group G] [MulAction G V]
    (N : Subgroup G) (x : V) : (stabilizerClosure N x).Normal := inferInstanceAs
      (Subgroup.normalClosure ((N ⊓ MulAction.stabilizer G x : Subgroup G) : Set G)).Normal

theorem stabilizerClosure_le {G V : Type*} [Group G] [MulAction G V]
    (N : Subgroup G) [N.Normal] (x : V) : stabilizerClosure N x ≤ N :=
  Subgroup.normalClosure_le_normal (fun _ h => h.1)

/-- Transitivity carries the stabilizer at the base vertex to every other one. -/
theorem normal_stabilizer_le_closure {G V : Type*} [Group G] [MulAction G V]
    (N : Subgroup G) [N.Normal] (x : V)
    (ht : ∀ u v : V, ∃ g : G, g • u = v) (y : V) :
    N ⊓ MulAction.stabilizer G y ≤ stabilizerClosure N x := by
  intro g hg
  obtain ⟨a, ha⟩ := ht x y
  have hc : a⁻¹ * g * a ∈ N := by
    simpa using Subgroup.Normal.conj_mem (inferInstance : N.Normal) g hg.1 a⁻¹
  have hf : (a⁻¹ * g * a) • x = x := by
    have hy : g • y = y := hg.2
    rw [mul_smul, mul_smul, ha, hy, ← ha, inv_smul_smul]
  have hm : a⁻¹ * g * a ∈ stabilizerClosure N x :=
    Subgroup.subset_normalClosure ⟨hc, hf⟩
  have h := Subgroup.Normal.conj_mem (inferInstance : (stabilizerClosure N x).Normal)
    (a⁻¹ * g * a) hm a
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h

/-- Fixing a normal orbit means agreeing at the vertex with some element of
the subgroup whose orbit is being collapsed. -/
theorem fixed_normal_orbit_iff {G V : Type*} [Group G] [MulAction G V]
    (L : Subgroup G) (g : G) (x : V) :
    (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel L V)) = Quotient.mk'' x ↔
      ∃ l : L, l • x = g • x := by
  rw [Quotient.eq'']
  exact MulAction.mem_orbit_iff

/-- The action on normal orbits has no residual stabilizer inside N/L. -/
theorem free_on_normal_orbits {G V : Type*} [Group G] [MulAction G V]
    (N L : Subgroup G) (hLN : L ≤ N)
    (hstab : ∀ x : V, N ⊓ MulAction.stabilizer G x ≤ L)
    (g : G) (hg : g ∈ N) (x : V)
    (hfix : (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel L V)) = Quotient.mk'' x) : g ∈ L := by
  obtain ⟨l, hl⟩ := (fixed_normal_orbit_iff L g x).mp hfix
  have hN : l.val⁻¹ * g ∈ N := N.mul_mem (N.inv_mem (hLN l.property)) hg
  have hf : (l.val⁻¹ * g) • x = x := by
    rw [mul_smul, ← hl]
    exact inv_smul_smul l.val x
  have hL := hstab x ⟨hN, hf⟩
  simpa only [mul_inv_cancel_left] using L.mul_mem l.property hL

/-- Factor an action through a normal subgroup acting trivially. -/
@[instance_reducible]
def actionThroughQuotient {G X : Type*} [Group G] [MulAction G X]
    (K : Subgroup G) [K.Normal] (hK : K ≤ (MulAction.toPermHom G X).ker) : MulAction (G ⧸ K) X :=
  MulAction.compHom X (QuotientGroup.lift K (MulAction.toPermHom G X) hK)

theorem actionThroughQuotient_mk_smul {G X : Type*} [Group G] [MulAction G X]
    (K : Subgroup G) [K.Normal] (hK : K ≤ (MulAction.toPermHom G X).ker) (g : G) (x : X) :
    letI := actionThroughQuotient K hK
    (QuotientGroup.mk g : G ⧸ K) • x = g • x := rfl

/-- Construct the genuine quotient-group action and prove its freeness, with
its compatibility with representatives made explicit. -/
theorem exists_free_quotient_action {G V : Type*} [Group G] [MulAction G V]
    (N L : Subgroup G) [L.Normal] (hLN : L ≤ N)
    (hstab : ∀ x : V, N ⊓ MulAction.stabilizer G x ≤ L) :
    ∃ a : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)),
      letI := a
      (∀ g : N ⧸ L.comap N.subtype, ∀ q : Quotient (MulAction.orbitRel L V),
        g • q = q → g = 1) ∧
      ∀ (g : N) (x : V), (QuotientGroup.mk g : N ⧸ L.comap N.subtype) • Quotient.mk'' x =
        (Quotient.mk'' (g.val • x) : Quotient (MulAction.orbitRel L V)) := by
  let Ω := Quotient (MulAction.orbitRel L V)
  let K := L.comap N.subtype
  let : MulAction G Ω := normalOrbitAction L
  have hK : K ≤ (MulAction.toPermHom N Ω).ker := by
    intro g hg
    apply Equiv.ext
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      change (Quotient.mk'' (g.val • x) : Ω) = Quotient.mk'' x
      apply Quotient.sound
      exact MulAction.mem_orbit x (⟨g.val, hg⟩ : L)
  let a := actionThroughQuotient K hK
  refine ⟨a, ?_, ?_⟩
  · intro g q hfix
    induction g using Quotient.inductionOn' with
    | h g =>
      induction q using Quotient.inductionOn with
      | _ x =>
        apply (QuotientGroup.eq_one_iff g).mpr
        exact free_on_normal_orbits N L hLN hstab g.val g.property x hfix
  · intro g x
    rfl

/-- Collapsing orbits loses at most the order of the acting subgroup. -/
theorem card_le_orbit_quotient_mul_group {L V : Type*} [Group L] [Fintype L]
    [Fintype V] [MulAction L V] [Fintype (Quotient (MulAction.orbitRel L V))] :
    Fintype.card V ≤ Fintype.card (Quotient (MulAction.orbitRel L V)) * Fintype.card L := by
  let Ω := Quotient (MulAction.orbitRel L V)
  let f : Ω × L → V := fun p => p.2 • p.1.out
  have hs : Function.Surjective f := by
    intro x
    let q : Ω := Quotient.mk'' x
    have he : (Quotient.mk'' x : Ω) = Quotient.mk'' q.out := (Quotient.out_eq q).symm
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
    exact ⟨(q, g), hg⟩
  simpa only [Fintype.card_prod] using Fintype.card_le_of_surjective f hs

/-- Under a transitive ambient action, the subgroup has at most its index
many orbits. The subgroup need not be normal. -/
theorem orbit_count_le_index {G V : Type*} [Group G] [Finite G] [MulAction G V]
    (N : Subgroup G) (x : V) (ht : ∀ u v : V, ∃ g : G, g • u = v) :
    Nat.card (Quotient (MulAction.orbitRel N V)) ≤ N.index := by
  let Ω := Quotient (MulAction.orbitRel N V)
  let f : G ⧸ N → Ω := fun q => Quotient.liftOn' q
    (fun g => Quotient.mk'' (g⁻¹ • x)) (by
      intro a b hab
      apply Quotient.sound
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩, ?_⟩
      change (a⁻¹ * b) • (b⁻¹ • x) = a⁻¹ • x
      simp only [mul_smul, smul_inv_smul])
  have hs : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ y =>
      obtain ⟨g, hg⟩ := ht x y
      refine ⟨QuotientGroup.mk g⁻¹, ?_⟩
      change (Quotient.mk'' ((g⁻¹)⁻¹ • x) : Ω) = Quotient.mk'' y
      simp only [inv_inv, hg]
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_surjective f hs

/-- Quotienting by L inside N preserves precisely the N-orbits. -/
noncomputable def quotient_orbit_equiv {G V : Type*} [Group G] [MulAction G V]
    (N L : Subgroup G) [L.Normal] (hLN : L ≤ N)
    (a : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)))
    (hcompat : letI := a
      ∀ (g : N) (x : V), (QuotientGroup.mk g : N ⧸ L.comap N.subtype) • Quotient.mk'' x =
        (Quotient.mk'' (g.val • x) : Quotient (MulAction.orbitRel L V))) :
    letI := a
    Quotient (MulAction.orbitRel N V) ≃
      Quotient (MulAction.orbitRel (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V))) := by
  letI := a
  let Ω := Quotient (MulAction.orbitRel L V)
  let K := L.comap N.subtype
  let π : V → Ω := Quotient.mk''
  let f : Quotient (MulAction.orbitRel N V) → Quotient (MulAction.orbitRel (N ⧸ K) Ω) :=
    Quotient.map π (by
      intro x y hxy
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hxy
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨QuotientGroup.mk g, (hcompat g y).trans (congrArg π hg)⟩)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q r h
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
        have ho : MulAction.orbitRel (N ⧸ K) Ω (π x) (π y) := Quotient.exact h
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp ho
        obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective K g
        have he : π (n.val • y) = π x := (hcompat n y).symm.trans hg
        obtain ⟨l, hl⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
        apply Quotient.sound
        apply MulAction.mem_orbit_iff.mpr
        refine ⟨⟨l.val⁻¹ * n.val, N.mul_mem (N.inv_mem (hLN l.property)) n.property⟩, ?_⟩
        change (l.val⁻¹ * n.val) • y = x
        rw [mul_smul, ← hl]
        exact inv_smul_smul l.val x
  · intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      induction p using Quotient.inductionOn with
      | _ x => exact ⟨Quotient.mk'' x, rfl⟩

theorem quotient_orbit_card_eq {G V : Type*} [Group G] [MulAction G V]
    (N L : Subgroup G) [L.Normal] (hLN : L ≤ N)
    (a : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)))
    (hcompat : letI := a
      ∀ (g : N) (x : V), (QuotientGroup.mk g : N ⧸ L.comap N.subtype) • Quotient.mk'' x =
        (Quotient.mk'' (g.val • x) : Quotient (MulAction.orbitRel L V))) :
    letI := a
    Nat.card (Quotient (MulAction.orbitRel (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)))) =
      Nat.card (Quotient (MulAction.orbitRel N V)) :=
  (Nat.card_congr (quotient_orbit_equiv N L hLN a hcompat)).symm

/-- All action and counting conclusions of stabilizer removal, for its
specified normal closure. Bounding the order of this closure is a separate
nilpotent-group obligation. -/
theorem stabilizer_removal_geometry {G V : Type*} [Group G] [Fintype G]
    [Fintype V] [MulAction G V] (N : Subgroup G) [N.Normal] (x : V)
    (ht : ∀ u v : V, ∃ g : G, g • u = v) :
    let L := stabilizerClosure N x
    L ≤ N ∧ ∃ a : MulAction (N ⧸ L.comap N.subtype) (Quotient (MulAction.orbitRel L V)),
      letI := a
      (∀ g : N ⧸ L.comap N.subtype, ∀ q : Quotient (MulAction.orbitRel L V), g • q = q → g = 1) ∧
      Nat.card (Quotient (MulAction.orbitRel (N ⧸ L.comap N.subtype)
        (Quotient (MulAction.orbitRel L V)))) ≤ N.index ∧
      Nat.card V ≤ Nat.card (Quotient (MulAction.orbitRel L V)) * Nat.card L := by
  let L := stabilizerClosure N x
  have hLN : L ≤ N := stabilizerClosure_le N x
  obtain ⟨a, hfree, hcompat⟩ := exists_free_quotient_action N L hLN (normal_stabilizer_le_closure N x ht)
  refine ⟨hLN, a, hfree, ?_, ?_⟩
  · rw [quotient_orbit_card_eq N L hLN a hcompat]
    exact orbit_count_le_index N x ht
  · let : Fintype (Quotient (MulAction.orbitRel L V)) := Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using (card_le_orbit_quotient_mul_group (L := L) (V := V))

end DirectedCycles
