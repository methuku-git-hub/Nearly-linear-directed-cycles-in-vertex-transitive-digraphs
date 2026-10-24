import DirectedCycles.FreeQuotient
import DirectedCycles.PermutationImage
import DirectedCycles.NilpotentRanks

set_option autoImplicit false
namespace DirectedCycles

/-- A normal subgroup acting freely bounds each ambient stabilizer by its index. -/
theorem stabilizer_card_le_index_of_free {G V : Type*} [Group G] [Finite G] [MulAction G V]
    (N : Subgroup G) [N.Normal] (x : V)
    (hf : ∀ g : N, g • x = x → g = 1) :
    Nat.card (MulAction.stabilizer G x) ≤ N.index := by
  let f := (QuotientGroup.mk' N).comp (MulAction.stabilizer G x).subtype
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_antisymm _ bot_le
    intro g hg
    change g = 1
    have hN : g.val ∈ N := (QuotientGroup.eq_one_iff g.val).mp hg
    have he := hf ⟨g.val,hN⟩ g.property
    have heval := congrArg (fun z : N => z.val) he
    exact Subtype.ext heval
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_injective f hi

/-- The surjective homomorphism to the actual action on normal orbits. -/
def normalOrbitImageHom {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) [H.Normal] :
    letI := normalOrbitAction (V := V) H
    G →* PermutationImage G (Quotient (MulAction.orbitRel H V)) :=
  letI := normalOrbitAction (V := V) H
  (MulAction.toPermHom G (Quotient (MulAction.orbitRel H V))).rangeRestrict

theorem normalOrbitImageHom_surjective {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) [H.Normal] :
    letI := normalOrbitAction (V := V) H
    Function.Surjective (normalOrbitImageHom (V := V) H) := by
  let : MulAction G (Quotient (MulAction.orbitRel H V)) := normalOrbitAction H
  exact MonoidHom.rangeRestrict_surjective _

theorem subgroup_le_normalOrbitImage_kernel {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) [H.Normal] :
    letI := normalOrbitAction (V := V) H
    H ≤ (normalOrbitImageHom (V := V) H).ker := by
  let : MulAction G (Quotient (MulAction.orbitRel H V)) := normalOrbitAction H
  intro g hg
  apply Subtype.ext
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    change (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel H V)) = Quotient.mk'' x
    exact Quotient.sound (MulAction.mem_orbit x (⟨g,hg⟩ : H))

/-- Killing all N-stabilizers makes the actual induced image of N free. -/
theorem induced_normal_subgroup_free {G V : Type*} [Group G] [MulAction G V]
    (N L : Subgroup G) [L.Normal] (hLN : L ≤ N)
    (hstab : ∀ x : V, N ⊓ MulAction.stabilizer G x ≤ L) :
    letI := normalOrbitAction (V := V) L
    let A := PermutationImage G (Quotient (MulAction.orbitRel L V))
    let M : Subgroup A := N.map (normalOrbitImageHom (V := V) L)
    ∀ g : M, ∀ q : Quotient (MulAction.orbitRel L V), g • q = q → g = 1 := by
  let Ω := Quotient (MulAction.orbitRel L V)
  let : MulAction G Ω := normalOrbitAction L
  let f := normalOrbitImageHom (V := V) L
  change ∀ g : N.map f, ∀ q : Ω, g • q = q → g = 1
  intro g q hfix
  obtain ⟨a,ha,hag⟩ := g.property
  apply Subtype.ext
  rw [← hag]
  induction q using Quotient.inductionOn with
  | _ x =>
    have hh : g.val • (Quotient.mk'' x : Ω) = Quotient.mk'' x := hfix
    rw [← hag] at hh
    have hL := free_on_normal_orbits N L hLN hstab a ha x hh
    exact subgroup_le_normalOrbitImage_kernel L hL

/-- Bound stabilizers after collapse independently of their original orders. -/
theorem induced_stabilizer_card_bound {G V : Type*} [Group G] [Finite G] [Finite V] [MulAction G V]
    (N L : Subgroup G) [N.Normal] [L.Normal] (hLN : L ≤ N)
    (hstab : ∀ x : V, N ⊓ MulAction.stabilizer G x ≤ L) :
    letI := normalOrbitAction (V := V) L
    let A := PermutationImage G (Quotient (MulAction.orbitRel L V))
    ∀ q : Quotient (MulAction.orbitRel L V), Nat.card (MulAction.stabilizer A q) ≤ N.index := by
  let Ω := Quotient (MulAction.orbitRel L V)
  let : MulAction G Ω := normalOrbitAction L
  let f := normalOrbitImageHom (V := V) L
  let M := N.map f
  have hf : Function.Surjective f := normalOrbitImageHom_surjective L
  let : M.Normal := Subgroup.Normal.map inferInstance f hf
  change ∀ q : Ω, Nat.card (MulAction.stabilizer (PermutationImage G Ω) q) ≤ N.index
  intro q
  have hfree := induced_normal_subgroup_free N L hLN hstab
  have hbound := stabilizer_card_le_index_of_free M q (fun g => hfree g q)
  exact hbound.trans (Nat.le_of_dvd (show 0 < N.index by rw [Subgroup.index_eq_card]; exact Nat.card_pos) (N.index_map_dvd hf))

end DirectedCycles
