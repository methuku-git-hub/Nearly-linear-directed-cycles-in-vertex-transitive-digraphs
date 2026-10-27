module

public import DirectedCycles.PathBranching
public import DirectedCycles.PathPrefixes

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A deterministic directed walk ending at a sink is uniquely determined
by its first and last vertices. No acyclicity assumption is needed. -/
theorem deterministic_chain_to_sink_unique {V : Type*} {R : Digraph V} {z : V}
    (hsink : ∀ v, ¬ R z v)
    (hdet : ∀ v x y, R v x → R v y → x = y)
    (l m : List V) (hl : l.IsChain R) (hm : m.IsChain R)
    (hhead : l.head? = m.head?)
    (hllast : l.getLast? = some z) (hmlast : m.getLast? = some z) : l = m := by
  induction l generalizing m with
  | nil => simp at hllast
  | cons a l ih =>
    cases m with
    | nil => simp at hmlast
    | cons b m =>
      have hab : a = b := by simpa using hhead
      subst b
      cases l with
      | nil =>
        have haz : a = z := by simpa using hllast
        subst a
        cases m with
        | nil => rfl
        | cons c m => exact (hsink c (List.isChain_cons_cons.mp hm).1).elim
      | cons c l =>
        cases m with
        | nil =>
          have haz : a = z := by simpa using hmlast
          subst a
          exact (hsink c (List.isChain_cons_cons.mp hl).1).elim
        | cons d m =>
          have hcd := hdet a c d (List.isChain_cons_cons.mp hl).1
            (List.isChain_cons_cons.mp hm).1
          congr 1
          apply ih (d :: m) (List.isChain_cons_cons.mp hl).2
            (List.isChain_cons_cons.mp hm).2
          · simp [hcd]
          · simpa using hllast
          · simpa using hmlast

namespace PartialOutBranching
variable {V : Type*} {D : Digraph V} {root : V} {U : Finset V}

theorem path_vertices_unique (B : PartialOutBranching D root U) {v : V}
    (P Q : SimplePath B.arc root v) : P.vertices = Q.vertices := by
  apply List.reverse_injective
  apply deterministic_chain_to_sink_unique B.root_no_in B.unique_in
    P.vertices.reverse Q.vertices.reverse
  · exact List.isChain_reverse.mpr P.chain
  · exact List.isChain_reverse.mpr Q.chain
  · simp [P.last,Q.last]
  · simp [P.head]
  · simp [Q.head]

/-- The canonical root path in a branching. Existence follows from the
branching invariant; uniqueness is proved independently above. -/
noncomputable def path (B : PartialOutBranching D root U) (v : V) (hv : v ∈ U) :
    SimplePath B.arc root v := Classical.choice (simplePath_of_reachable (B.reachable v hv))

theorem path_eq (B : PartialOutBranching D root U) {v : V} (hv : v ∈ U)
    (P : SimplePath B.arc root v) : (B.path v hv).vertices = P.vertices :=
  B.path_vertices_unique _ _

/-- A prefix of a tree path is the unique tree path to its final vertex. -/
theorem path_prefix (B : PartialOutBranching D root U) {v w : V}
    (hv : v ∈ U) (hw : w ∈ U) (hmem : w ∈ (B.path v hv).vertices) :
    (B.path w hw).vertices <+: (B.path v hv).vertices := by
  obtain ⟨R,hR,_,hnd,hc,hh,hl⟩ := prefix_through_vertex
    (B.path v hv).vertices (B.path v hv).nodup (B.path v hv).chain
    (B.path v hv).head hmem
  let P : SimplePath B.arc root w := ⟨R,hnd,hh,hl,hc⟩
  have he := B.path_eq hw P
  change (B.path w hw).vertices = R at he
  rw [he]
  exact hR

theorem root_path (B : PartialOutBranching D root U) :
    (B.path root B.root_mem).vertices = [root] :=
  B.path_eq B.root_mem ⟨[root],by simp,rfl,rfl,.singleton root⟩

theorem path_append_of_arc (B : PartialOutBranching D root U) {x y : V}
    (hx : x ∈ U) (hy : y ∈ U) (hxy : B.arc x y) :
    (B.path y hy).vertices = (B.path x hx).vertices ++ [y] := by
  let P := B.path y hy
  have hry : root ≠ y := by intro he; exact B.root_no_in x (he ▸ hxy)
  have hne := P.dropLast_nonempty hry
  let z := P.vertices.dropLast.getLast hne
  have hz : P.vertices.dropLast.getLast? = some z := List.getLast?_eq_some_getLast hne
  have hzy := P.dropLast_last_arc z hz
  have hzx : z = x := B.unique_in y z x hzy hxy
  let Q : SimplePath B.arc root x :=
    ⟨P.vertices.dropLast,P.nodup.sublist (List.dropLast_sublist _),P.dropLast_head hry,
      by simp only [hz,hzx],P.chain.dropLast⟩
  have he := B.path_eq hx Q
  change (B.path x hx).vertices = P.vertices.dropLast at he
  rw [he]
  exact P.eq_dropLast_append

end PartialOutBranching

namespace SimplePath
variable {V : Type*} {D : Digraph V} {x y : V}

def reverse (P : SimplePath D x y) : SimplePath (fun a b => D b a) y x where
  vertices := P.vertices.reverse
  nodup := List.nodup_reverse.mpr P.nodup
  head := by simpa using P.last
  last := by simpa using P.head
  chain := List.isChain_reverse.mpr P.chain

end SimplePath

/-- Prescribed root paths extend independently to inward and outward
branchings. Each branching supplies unique, consistent paths. -/
theorem branchings_containing_paths {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} {root u v : V} (P : SimplePath D root u) (Z : SimplePath D v root)
    (hsc : StronglyConnected D) :
    ∃ B : PartialOutBranching D root Finset.univ,
    ∃ A : PartialOutBranching (fun x y => D y x) root Finset.univ,
    P.vertices.IsChain B.arc ∧ Z.vertices.IsChain (fun x y => A.arc y x) := by
  obtain ⟨B,hB⟩ := out_branching_containing_path P hsc
  have hrev : StronglyConnected (fun x y => D y x) := by
    intro x y
    exact (hsc y x).swap
  obtain ⟨A,hA⟩ := out_branching_containing_path Z.reverse hrev
  exact ⟨B,A,hB,List.isChain_reverse.mp hA⟩

end DirectedCycles
