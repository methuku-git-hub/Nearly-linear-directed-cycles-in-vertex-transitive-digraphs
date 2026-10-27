module

public import DirectedCycles.TrailEdges

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

theorem arcSet_out_degree {V : Type*} [Fintype V] (D : Digraph V) (v : V) :
    ((arcSet D).filter (fun e => e.1 = v)).card = (Finset.univ.filter (D v)).card := by
  symm
  apply Finset.card_bij (fun y _ => (v, y))
  · intro y hy
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, mem_arcSet, and_true]
      using hy
  · intro y _ z _ he
    exact congrArg Prod.snd he
  · rintro ⟨a, b⟩ he
    simp only [Finset.mem_filter, mem_arcSet] at he
    obtain ⟨hab, rfl⟩ := he
    exact ⟨b, by simp [hab], rfl⟩

theorem arcSet_in_degree {V : Type*} [Fintype V] (D : Digraph V) (v : V) :
    ((arcSet D).filter (fun e => e.2 = v)).card =
      (Finset.univ.filter (fun u => D u v)).card := by
  symm
  apply Finset.card_bij (fun u _ => (u, v))
  · intro u hu
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, mem_arcSet, and_true]
      using hu
  · intro y _ z _ he
    exact congrArg Prod.fst he
  · rintro ⟨a, b⟩ he
    simp only [Finset.mem_filter, mem_arcSet] at he
    obtain ⟨hab, rfl⟩ := he
    exact ⟨a, by simp [hab], rfl⟩

theorem balanced_of_equal_degrees {V : Type*} [Fintype V] (D : Digraph V)
    (h : ∀ v, (Finset.univ.filter (D v)).card =
      (Finset.univ.filter (fun u => D u v)).card) : Balanced D := by
  intro v
  rw [arcSet_out_degree, arcSet_in_degree, h v]

theorem arcSet_card_regular {V : Type*} [Fintype V] (D : Digraph V) (d : ℕ)
    (hd : ∀ v, (Finset.univ.filter (D v)).card = d) :
    (arcSet D).card = Fintype.card V * d := by
  calc (arcSet D).card = ∑ v : V, ((arcSet D).filter (fun e => e.1 = v)).card :=
         Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
       _ = Fintype.card V * d := by simp [arcSet_out_degree, hd]

theorem Walk.end_eq_of_edges_nil {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) (h : W.edges = []) : x = y := by
  cases W with
  | nil => rfl
  | cons W e => simp [Walk.edges] at h

theorem Walk.first_edge_tail {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) : ∀ e ∈ W.edges.head?, e.1 = x := by
  induction W with
  | nil => simp [Walk.edges]
  | @cons a b W h ih =>
    by_cases hn : W.edges = []
    · have hxa := W.end_eq_of_edges_nil hn
      subst a
      simpa only [Walk.edges, hn, List.nil_append, List.head?_cons, Option.mem_some_iff]
        using (fun e (he : (x, b) = e) => (congrArg Prod.fst he).symm)
    · simpa only [Walk.edges, List.head?_append_of_ne_nil _ hn] using ih

theorem Walk.last_edge_head {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) : ∀ e ∈ W.edges.getLast?, e.2 = y := by
  cases W with
  | nil => simp [Walk.edges]
  | cons W h => simp [Walk.edges]

theorem Walk.edges_chain {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) : W.edges.IsChain (fun e f => e.2 = f.1) := by
  induction W with
  | nil => exact .nil
  | @cons a b W h ih =>
    apply ih.append (.singleton (a, b))
    intro e he f hf
    have hf' : f = (a, b) := by simpa using hf.symm
    subst f
    exact W.last_edge_head e he

theorem Walk.closed_edges_circular {V : Type*} {D : Digraph V} {x : V}
    (W : Walk D x x) : CircularChain (fun e f => e.2 = f.1) W.edges := by
  refine ⟨W.edges_chain, ?_⟩
  intro e he f hf
  exact (W.last_edge_head e he).trans (W.first_edge_tail f hf).symm

/-- Circular adjacency for a list does not require its entries to be distinct. -/
theorem circularChain_get {V : Type*} {D : Digraph V} (l : List V)
    (hl : 2 ≤ l.length) (ha : CircularChain D l) (i : Fin l.length) :
    D (l.get i) (l.get (finRotate l.length i)) := by
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

/-- Circular adjacency also includes a one-entry loop. -/
theorem circularChain_get_nonempty {V : Type*} {D : Digraph V} (l : List V)
    (hl : 0 < l.length) (ha : CircularChain D l) (i : Fin l.length) :
    D (l.get i) (l.get (finRotate l.length i)) := by
  by_cases htwo : 2 ≤ l.length
  · exact circularChain_get l htwo ha i
  · have hone : l.length = 1 := by omega
    cases l with
    | nil => simp at hone
    | cons v vs =>
      have hv : vs = [] := List.length_eq_zero_iff.mp (by simpa using hone)
      subst vs
      have hh := ha.2 v (by simp) v (by simp)
      simpa using hh

/-- A regular directed Euler tour in the cyclic indexing used by the path
sampling construction. Its consecutive ordered pairs biject with the arcs. -/
theorem regular_directed_euler_sequence {V : Type*} [Fintype V] (D : Digraph V)
    (hD : StronglyConnected D) (d : ℕ) (hdpos : 0 < d) (hq : 0 < Fintype.card V)
    (hout : ∀ v, (Finset.univ.filter (D v)).card = d)
    (hin : ∀ v, (Finset.univ.filter (fun u => D u v)).card = d) :
    ∃ N : ℕ, ∃ A : Fin N → V, N = Fintype.card V * d ∧
      ∃ hA : ∀ i, D (A i) (A (finRotate N i)),
        Function.Bijective (fun i => (⟨(A i, A (finRotate N i)), hA i⟩ : {e : V × V // D e.1 e.2})) := by
  have hbal : Balanced D := balanced_of_equal_degrees D (fun v => (hout v).trans (hin v).symm)
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨W, hn, hall⟩ := directed_euler_tour D hbal hD x
  have heq : W.edges.toFinset = arcSet D := by
    ext e
    simp only [List.mem_toFinset, mem_arcSet]
    exact ⟨fun h => W.edge_mem h, fun h => hall e.1 e.2 h⟩
  have hlen : W.edges.length = Fintype.card V * d := by
    rw [← List.toFinset_card_of_nodup hn, heq, arcSet_card_regular D d hout]
  have hpos : 0 < W.edges.length := by rw [hlen]; positivity
  let A : Fin W.edges.length → V := fun i => (W.edges.get i).1
  have hadj : ∀ i, (W.edges.get i).2 = A (finRotate W.edges.length i) :=
    circularChain_get_nonempty W.edges hpos W.closed_edges_circular
  have hpair : ∀ i, (A i, A (finRotate W.edges.length i)) = W.edges.get i := by
    intro i
    rw [← hadj i]
  have ha : ∀ i, D (A i) (A (finRotate W.edges.length i)) := by
    intro i
    have hm := W.edge_mem (List.get_mem W.edges i)
    rw [← hpair i] at hm
    exact hm
  refine ⟨W.edges.length, A, hlen, ha, ?_, ?_⟩
  · intro i j hij
    apply List.nodup_iff_injective_get.mp hn
    have hh := congrArg Subtype.val hij
    simpa only [hpair] using hh
  · intro e
    have hm : e.val ∈ W.edges := hall e.val.1 e.val.2 e.property
    obtain ⟨i, hi⟩ := List.get_of_mem hm
    refine ⟨i, Subtype.ext ?_⟩
    exact (hpair i).trans hi

end DirectedCycles
