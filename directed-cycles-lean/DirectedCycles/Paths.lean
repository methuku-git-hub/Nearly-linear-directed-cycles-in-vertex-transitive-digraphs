module

public import DirectedCycles.Basic
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.Nodup

@[expose] public section

set_option autoImplicit false

namespace DirectedCycles

/-- Adjacency around a finite list, including its closing edge. -/
def CircularChain {V : Type*} (D : Digraph V) (l : List V) : Prop :=
  l.IsChain D ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, D x y

/-- A list with distinct vertices and circular adjacency is a simple cycle. -/
def cycleOfList {V : Type*} {D : Digraph V} (l : List V)
    (hn : l.Nodup) (hl : 2 ≤ l.length) (ha : CircularChain D l) : Cycle D where
  length := l.length
  two_le := hl
  vertex := ⟨l.get, List.nodup_iff_injective_get.mp hn⟩
  arc i := by
    let : NeZero l.length := ⟨by omega⟩
    rw [finRotate_apply]
    change D (l.get i) (l.get (i + 1))
    by_cases hi : i.val + 1 < l.length
    · have hv : (i + 1 : Fin l.length).val = i.val + 1 := by
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < l.length by omega),
          Nat.mod_eq_of_lt hi]
      simpa only [List.get_eq_getElem, hv] using ha.1.getElem i.val hi
    · have hlast : i.val = l.length - 1 := by omega
      have hz : (i + 1 : Fin l.length).val = 0 := by
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < l.length by omega),
          show i.val + 1 = l.length by omega]
      apply ha.2
      · simp [List.getLast?_eq_getElem?, hlast]
      · simp [List.head?_eq_getElem?, hz, show 0 < l.length by omega]

theorem circularChain_ofFn {V : Type*} {D : Digraph V} {n : ℕ}
    (f : Fin n → V) (h : ∀ i, D (f i) (f (finRotate n i))) :
    CircularChain D (List.ofFn f) := by
  constructor
  · apply List.isChain_ofFn.mpr
    intro i hi
    have hn : 0 < n := by omega
    let : NeZero n := ⟨by omega⟩
    have he : finRotate n ⟨i, by omega⟩ = ⟨i + 1, hi⟩ := by
      apply Fin.ext
      simp [finRotate_apply, Fin.val_add, Nat.mod_eq_of_lt (show 1 < n by omega),
        Nat.mod_eq_of_lt hi]
    simpa only [he] using h ⟨i, by omega⟩
  · cases n with
    | zero => simp
    | succ n =>
      intro x hx y hy
      have hx' : x = f (Fin.last n) := by
        simpa only [List.getLast?_eq_getElem?, List.length_ofFn, Nat.add_sub_cancel,
          List.getElem?_ofFn, dite_eq_left (Nat.lt_succ_self n), Fin.last,
          Option.some.injEq] using hx.symm
      have hy' : y = f 0 := by
        simpa [List.head?_eq_getElem?, List.getElem?_eq_getElem] using hy.symm
      subst x; subst y
      simpa only [finRotate_last] using h (Fin.last n)

private theorem head_flatten {V : Type*} (L : List (List V)) (hne : [] ∉ L) :
    L.flatten.head? = L.head?.bind List.head? := by
  cases L with
  | nil => rfl
  | cons l L =>
    have hl : l ≠ [] := by intro h; exact hne (by simp [h])
    simp [List.flatten_cons, List.head?_append_of_ne_nil _ hl]

private theorem last_flatten {V : Type*} (L : List (List V)) (hne : [] ∉ L) :
    L.flatten.getLast? = L.getLast?.bind List.getLast? := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L l ih =>
    have hl : l ≠ [] := by intro h; exact hne (by simp [h])
    simp [List.flatten_append, List.getLast?_append_of_ne_nil _ hl]

/-- Concatenation preserves circular adjacency when each segment is a chain
and the last vertex of each segment points to the first of its successor. -/
theorem circularChain_flatten {V : Type*} {D : Digraph V} (L : List (List V))
    (hne : [] ∉ L) (hin : ∀ l ∈ L, l.IsChain D)
    (hjoin : CircularChain
      (fun l m => ∀ x ∈ l.getLast?, ∀ y ∈ m.head?, D x y) L) :
    CircularChain D L.flatten := by
  constructor
  · exact (List.isChain_flatten hne).mpr ⟨hin, hjoin.1⟩
  · rw [head_flatten L hne, last_flatten L hne]
    intro x hx y hy
    obtain ⟨l, hl, hx⟩ := Option.mem_bind_iff.mp hx
    obtain ⟨m, hm, hy⟩ := Option.mem_bind_iff.mp hy
    exact hjoin.2 l hl m hm x hx y hy

/-- Disjoint nonempty path segments arranged cyclically give a cycle containing
all their vertices, with length equal to the sum of their lengths as lists. -/
theorem cycle_of_disjoint_segments {V : Type*} {D : Digraph V} {s : ℕ}
    (hs : 2 ≤ s) (P : Fin s → List V)
    (hne : ∀ i, P i ≠ []) (hnd : ∀ i, (P i).Nodup)
    (hd : ∀ i j, i ≠ j → (P i).Disjoint (P j))
    (hin : ∀ i, (P i).IsChain D)
    (hj : ∀ i, ∀ x ∈ (P i).getLast?,
      ∀ y ∈ (P (finRotate s i)).head?, D x y) :
    ∃ C : Cycle D, C.length = ∑ i, (P i).length ∧ s ≤ C.length ∧
      List.ofFn C.vertex = (List.ofFn P).flatten := by
  let L := List.ofFn P
  have hne' : [] ∉ L := by
    simp only [L, List.mem_ofFn]
    rintro ⟨i, hi⟩
    exact hne i hi
  have hin' : ∀ l ∈ L, l.IsChain D := by
    intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact hin i
  have hnd' : L.flatten.Nodup := by
    apply List.nodup_flatten.mpr
    constructor
    · intro l hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      exact hnd i
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      exact hd i j (ne_of_lt hij)
  have hlength : L.flatten.length = ∑ i, (P i).length := by
    simp [L, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  have hle : s ≤ L.flatten.length := by
    rw [hlength]
    calc s = ∑ _i : Fin s, 1 := by simp
         _ ≤ ∑ i : Fin s, (P i).length := Finset.sum_le_sum (fun i _ => by
           have := List.length_pos_iff.mpr (hne i)
           omega)
  have hchain := circularChain_flatten L hne' hin' (circularChain_ofFn P hj)
  refine ⟨cycleOfList L.flatten hnd' (hs.trans hle) hchain, hlength, hle, ?_⟩
  exact List.ofFn_get L.flatten

/-- A simple directed path includes both endpoints. The singleton list is the
path of length zero. -/
structure SimplePath {V : Type*} (D : Digraph V) (x y : V) where
  vertices : List V
  nodup : vertices.Nodup
  head : vertices.head? = some x
  last : vertices.getLast? = some y
  chain : vertices.IsChain D

def SimplePath.length {V : Type*} {D : Digraph V} {x y : V}
    (P : SimplePath D x y) : ℕ := P.vertices.length - 1

theorem SimplePath.nonempty {V : Type*} {D : Digraph V} {x y : V}
    (P : SimplePath D x y) : P.vertices ≠ [] := by
  intro h
  have := P.head
  simp [h] at this

/-- Erasing loops from an arbitrary directed walk preserves its endpoints. -/
theorem simplePath_of_reachable {V : Type*} {D : Digraph V} {x y : V}
    (h : Reachable D x y) : Nonempty (SimplePath D x y) := by
  classical
  induction h with
  | refl => exact ⟨⟨[x], by simp, rfl, rfl, .singleton x⟩⟩
  | @tail z y h hzy ih =>
    obtain ⟨P⟩ := ih
    by_cases hy : y ∈ P.vertices
    · obtain ⟨l, r, he⟩ := List.mem_iff_append.mp hy
      have he' : P.vertices = (l ++ [y]) ++ r := by simpa using he
      have hn := P.nodup
      have hc := P.chain
      rw [he'] at hn hc
      refine ⟨⟨l ++ [y], List.nodup_append.mp hn |>.1, ?_, by simp,
        hc.left_of_append⟩⟩
      have hh := P.head
      rw [he] at hh
      cases l <;> simpa using hh
    · refine ⟨⟨P.vertices ++ [y], ?_, ?_, by simp, ?_⟩⟩
      · apply P.nodup.append (by simp)
        simpa using hy
      · simpa only [List.head?_append_of_ne_nil _ P.nonempty] using P.head
      · apply P.chain.append (.singleton y)
        intro a ha b hb
        have ha' : a = z := by simpa only [P.last, Option.mem_some_iff, eq_comm] using ha
        have hb' : b = y := by simpa [eq_comm] using hb
        subst a; subst b
        exact hzy

/-- Applying an injective arc map to a simple path preserves its simplicity. -/
def SimplePath.map {V W : Type*} {D : Digraph V} {E : Digraph W} {x y : V}
    (P : SimplePath D x y) (f : V ↪ W)
    (hf : ∀ a b, D a b → E (f a) (f b)) : SimplePath E (f x) (f y) where
  vertices := P.vertices.map f
  nodup := P.nodup.map f.injective
  head := by simp [List.head?_map, P.head]
  last := by simp [List.getLast?_map, P.last]
  chain := by
    rw [List.isChain_map]
    exact P.chain.imp hf

theorem SimplePath.eq_dropLast_append {V : Type*} {D : Digraph V} {x y : V}
    (P : SimplePath D x y) : P.vertices = P.vertices.dropLast ++ [y] := by
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp P.last
  simp [hl]

theorem SimplePath.dropLast_nonempty {V : Type*} {D : Digraph V} {x y : V}
    (P : SimplePath D x y) (hxy : x ≠ y) : P.vertices.dropLast ≠ [] := by
  intro he
  have hv : P.vertices = [y] := by simpa [he] using P.eq_dropLast_append
  have hh := P.head
  simp only [hv, List.head?_cons, Option.some.injEq] at hh
  exact hxy hh.symm

theorem SimplePath.dropLast_head {V : Type*} {D : Digraph V} {x y : V}
    (P : SimplePath D x y) (hxy : x ≠ y) : P.vertices.dropLast.head? = some x := by
  have hh := P.head
  rw [P.eq_dropLast_append, List.head?_append_of_ne_nil _ (P.dropLast_nonempty hxy)] at hh
  exact hh

theorem SimplePath.dropLast_last_arc {V : Type*} {D : Digraph V} {x y : V}
    (P : SimplePath D x y) : ∀ a ∈ P.vertices.dropLast.getLast?, D a y := by
  have hc := P.chain
  rw [P.eq_dropLast_append] at hc
  intro a ha
  exact (List.isChain_append.mp hc).2.2 a ha y (by simp)

theorem Cycle.successor_ne {V : Type*} {D : Digraph V} (C : Cycle D)
    (i : Fin C.length) : C.vertex i ≠ C.vertex (finRotate C.length i) := by
  intro he
  have h := C.vertex.injective he
  let : NeZero C.length := ⟨by have := C.two_le; omega⟩
  rw [finRotate_apply] at h
  have ho : (1 : Fin C.length) = 0 := add_left_cancel (h.symm.trans (add_zero i).symm)
  have hv := congrArg Fin.val ho
  have ht := C.two_le
  change 1 % C.length = 0 at hv
  rw [Nat.mod_eq_of_lt (show 1 < C.length by omega)] at hv
  omega

theorem Cycle.successor_injective {V : Type*} {D : Digraph V} (C : Cycle D) :
    Function.Injective (fun i => C.vertex (finRotate C.length i)) :=
  C.vertex.injective.comp (finRotate C.length).injective

/-- Manuscript Lemma 5.8. The original cycle may belong to a different digraph
on the same vertices. Its edges are replaced by the specified paths in `D`. -/
theorem walk_expansion {V : Type*} {D Q : Digraph V} (C : Cycle Q)
    (τ : Fin C.length → V)
    (P : ∀ i, SimplePath D (C.vertex i) (C.vertex (finRotate C.length i)))
    (hinter : ∀ i j v, v ∈ (P i).vertices.dropLast → v ∈ (P j).vertices.dropLast →
      C.vertex i = C.vertex j ∨
      C.vertex (finRotate C.length i) = C.vertex (finRotate C.length j) ∨
      C.vertex (finRotate C.length j) = τ i ∨
      C.vertex (finRotate C.length i) = τ j)
    (hτ : ∀ i j, τ i = C.vertex j → j = finRotate C.length i) :
    ∃ L : Cycle D, L.length = ∑ i, (P i).length ∧ C.length ≤ L.length ∧
      List.ofFn L.vertex = (List.ofFn (fun i => (P i).vertices.dropLast)).flatten := by
  simp only [SimplePath.length, ← List.length_dropLast]
  apply cycle_of_disjoint_segments C.two_le (fun i => (P i).vertices.dropLast)
    (fun i => (P i).dropLast_nonempty (C.successor_ne i))
    (fun i => (P i).nodup.sublist (List.dropLast_sublist _))
  · intro i j hij
    apply List.disjoint_left.mpr
    intro v hv hjv
    rcases hinter i j v hv hjv with he | he | he | he
    · exact hij (C.vertex.injective he)
    · exact hij ((finRotate C.length).injective (C.vertex.injective he))
    · exact hij ((finRotate C.length).injective (hτ i _ he.symm)).symm
    · exact hij ((finRotate C.length).injective (hτ j _ he.symm))
  · exact fun i => (P i).chain.dropLast
  · intro i x hx y hy
    have hy' : y = C.vertex (finRotate C.length i) := by
      simpa only [(P _).dropLast_head (C.successor_ne _), Option.mem_some_iff,
        eq_comm] using hy
    subst y
    exact (P i).dropLast_last_arc x hx

end DirectedCycles
