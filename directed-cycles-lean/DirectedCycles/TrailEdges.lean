import DirectedCycles.BoundedWalks

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Ordered arcs traversed by a walk, retaining multiplicities and order. -/
def Walk.edges {V : Type*} {D : Digraph V} {x y : V} : Walk D x y → List (V × V)
  | .nil => []
  | @Walk.cons _ _ _ y z W _ => W.edges ++ [(y, z)]

@[simp] theorem Walk.edges_length {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) : W.edges.length = W.length := by
  induction W with
  | nil => rfl
  | cons W h ih => simp [Walk.edges, Walk.length, ih]

@[simp] theorem Walk.edges_comp {V : Type*} {D : Digraph V} {x y z : V}
    (P : Walk D x y) (Q : Walk D y z) : (P.comp Q).edges = P.edges ++ Q.edges := by
  induction Q with
  | nil => simp [Walk.comp, Walk.edges]
  | cons Q h ih => simp [Walk.comp, Walk.edges, ih, List.append_assoc]

theorem Walk.edge_mem {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) {a b : V} (h : (a, b) ∈ W.edges) : D a b := by
  induction W with
  | nil => simp [Walk.edges] at h
  | @cons y z W e ih =>
    simp only [Walk.edges, List.mem_append, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with h | ⟨rfl, rfl⟩
    · exact ih h
    · exact e

/-- Conservation of traversals at a vertex, with the two endpoint corrections. -/
theorem Walk.edge_balance {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) (v : V) :
    (W.edges.filter (fun e => decide (e.1 = v))).length + (if y = v then 1 else 0) =
      (W.edges.filter (fun e => decide (e.2 = v))).length + (if x = v then 1 else 0) := by
  induction W with
  | nil => simp [Walk.edges]
  | @cons y z W e ih =>
    simp only [Walk.edges, List.filter_append, List.length_append]
    by_cases hx : x = v <;> by_cases hy : y = v <;> by_cases hz : z = v <;>
      simp_all

noncomputable def arcSet {V : Type*} [Fintype V] (D : Digraph V) : Finset (V × V) :=
  Finset.univ.filter (fun e => D e.1 e.2)

@[simp] theorem mem_arcSet {V : Type*} [Fintype V] (D : Digraph V) (e : V × V) :
    e ∈ arcSet D ↔ D e.1 e.2 := by simp [arcSet]

/-- An edge-simple walk uses at most the number of arcs of the graph. -/
theorem Walk.trail_length_le {V : Type*} [Fintype V] {D : Digraph V} {x y : V}
    (W : Walk D x y) (hn : W.edges.Nodup) : W.length ≤ (arcSet D).card := by
  have hs : W.edges.toFinset ⊆ arcSet D := by
    intro e he
    exact (mem_arcSet _ _).mpr (W.edge_mem (List.mem_toFinset.mp he))
  have hh := Finset.card_le_card hs
  simpa only [List.toFinset_card_of_nodup hn, W.edges_length] using hh

/-- There is a longest edge-simple walk from each prescribed vertex. -/
theorem longest_trail {V : Type*} [Fintype V] (D : Digraph V) (x : V) :
    ∃ y, ∃ W : Walk D x y, W.edges.Nodup ∧
      ∀ z (P : Walk D x z), P.edges.Nodup → P.length ≤ W.length := by
  let possible : ℕ → Prop := fun n => ∃ y, ∃ W : Walk D x y, W.edges.Nodup ∧ W.length = n
  have hz : possible 0 := ⟨x, .nil, by simp [Walk.edges], rfl⟩
  obtain ⟨y, W, hW, hwlen⟩ := Nat.findGreatest_spec (Nat.zero_le (arcSet D).card) hz
  refine ⟨y, W, hW, ?_⟩
  intro z P hP
  rw [hwlen]
  exact Nat.le_findGreatest (P.trail_length_le hP) ⟨z, P, hP, rfl⟩


/-- Filtered traversal counts equal the corresponding finite-set counts for a trail. -/
theorem Walk.filter_edge_count {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) (hn : W.edges.Nodup) (p : V × V → Prop) :
    (W.edges.filter (fun e => decide (p e))).length = (W.edges.toFinset.filter p).card := by
  rw [← List.toFinset_card_of_nodup (hn.filter _), List.toFinset_filter]
  simp

/-- A longest trail has exhausted every outgoing arc at its final vertex. -/
theorem longest_trail_exhausts_endpoint {V : Type*} [Fintype V] (D : Digraph V)
    {x y : V} (W : Walk D x y) (hn : W.edges.Nodup)
    (hmax : ∀ z (P : Walk D x z), P.edges.Nodup → P.length ≤ W.length) :
    ∀ z, D y z → (y, z) ∈ W.edges := by
  intro z hyz
  by_contra hz
  have hnd : (W.cons hyz).edges.Nodup := by
    simpa [Walk.edges] using hn.concat hz
  have hm := hmax z (W.cons hyz) hnd
  simp only [Walk.length] at hm
  omega

/-- Balance is stated as equality of incoming and outgoing arc counts. -/
def Balanced {V : Type*} [Fintype V] (D : Digraph V) : Prop :=
  ∀ v, ((arcSet D).filter (fun e => e.1 = v)).card =
    ((arcSet D).filter (fun e => e.2 = v)).card

/-- In a balanced digraph, an edge-simple walk that has exhausted its final
vertex must finish where it started. -/
theorem exhausted_trail_closed {V : Type*} [Fintype V] (D : Digraph V)
    (hbal : Balanced D) {x y : V} (W : Walk D x y) (hn : W.edges.Nodup)
    (hex : ∀ z, D y z → (y, z) ∈ W.edges) : x = y := by
  have heq : W.edges.toFinset.filter (fun e => e.1 = y) =
      (arcSet D).filter (fun e => e.1 = y) := by
    ext e
    simp only [Finset.mem_filter, List.mem_toFinset, mem_arcSet]
    constructor
    · exact fun h => ⟨W.edge_mem h.1, h.2⟩
    · rintro ⟨he, htail⟩
      exact ⟨by simpa only [← htail, Prod.eta] using hex e.2 (by simpa [htail] using he), htail⟩
  have hsub : W.edges.toFinset.filter (fun e => e.2 = y) ⊆
      (arcSet D).filter (fun e => e.2 = y) := by
    intro e he
    simp only [Finset.mem_filter, List.mem_toFinset, mem_arcSet] at he ⊢
    exact ⟨W.edge_mem he.1, he.2⟩
  have hc := Finset.card_le_card hsub
  have hb := W.edge_balance y
  rw [W.filter_edge_count hn, W.filter_edge_count hn, heq, hbal y] at hb
  by_contra hxy
  simp only [ite_true] at hb
  simp only [hxy, ite_false] at hb
  omega

/-- Every longest trail in a balanced finite digraph is closed. -/
theorem longest_closed_trail {V : Type*} [Fintype V] (D : Digraph V)
    (hbal : Balanced D) (x : V) :
    ∃ W : Walk D x x, W.edges.Nodup ∧
      ∀ z (P : Walk D x z), P.edges.Nodup → P.length ≤ W.length := by
  obtain ⟨y, W, hn, hm⟩ := longest_trail D x
  have he := exhausted_trail_closed D hbal W hn (longest_trail_exhausts_endpoint D W hn hm)
  subst y
  exact ⟨W, hn, hm⟩

/-- Splitting at the tail of any occurrence of an arc. -/
theorem Walk.split_at_edge_tail {V : Type*} {D : Digraph V} {x y a b : V}
    (W : Walk D x y) (h : (a, b) ∈ W.edges) :
    ∃ P : Walk D x a, ∃ Q : Walk D a y, W.edges = P.edges ++ Q.edges := by
  induction W with
  | nil => simp [Walk.edges] at h
  | @cons u v W e ih =>
    simp only [Walk.edges, List.mem_append, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with h | ⟨rfl, rfl⟩
    · obtain ⟨P, Q, hPQ⟩ := ih h
      exact ⟨P, Q.cons e, by simp [Walk.edges, hPQ, List.append_assoc]⟩
    · exact ⟨W, Walk.cons .nil e, by simp [Walk.edges]⟩

/-- Splitting at the head of any occurrence of an arc. -/
theorem Walk.split_at_edge_head {V : Type*} {D : Digraph V} {x y a b : V}
    (W : Walk D x y) (h : (a, b) ∈ W.edges) :
    ∃ P : Walk D x b, ∃ Q : Walk D b y, W.edges = P.edges ++ Q.edges := by
  induction W with
  | nil => simp [Walk.edges] at h
  | @cons u v W e ih =>
    simp only [Walk.edges, List.mem_append, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with h | ⟨rfl, rfl⟩
    · obtain ⟨P, Q, hPQ⟩ := ih h
      exact ⟨P, Q.cons e, by simp [Walk.edges, hPQ, List.append_assoc]⟩
    · exact ⟨W.cons e, .nil, by simp [Walk.edges]⟩


@[simp] theorem Walk.edges_map {V U : Type*} {D : Digraph V} {E : Digraph U} {x y : V}
    (W : Walk D x y) (f : V → U) (hf : ∀ a b, D a b → E (f a) (f b)) :
    (W.map f hf).edges = W.edges.map (fun e => (f e.1, f e.2)) := by
  induction W with
  | nil => rfl
  | @cons a b W e ih =>
    simpa [Walk.map, Walk.edges] using congrArg (fun l => l ++ [(f a, f b)]) ih

/-- Deleting the arcs of a closed trail preserves degree balance. -/
theorem residual_balanced {V : Type*} [Fintype V] (D : Digraph V)
    (hbal : Balanced D) {x : V} (W : Walk D x x) (hn : W.edges.Nodup) :
    Balanced (fun a b => D a b ∧ (a, b) ∉ W.edges) := by
  let R : Digraph V := fun a b => D a b ∧ (a, b) ∉ W.edges
  have hs : W.edges.toFinset ⊆ arcSet D := by
    intro e he
    exact (mem_arcSet _ _).mpr (W.edge_mem (List.mem_toFinset.mp he))
  have hfilter (p : V × V → Prop) : (arcSet R).filter p =
      (arcSet D).filter p \ W.edges.toFinset.filter p := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff, mem_arcSet, List.mem_toFinset, R]
    tauto
  intro v
  have hb := W.edge_balance v
  rw [W.filter_edge_count hn, W.filter_edge_count hn] at hb
  have he : (W.edges.toFinset.filter (fun e => e.1 = v)).card =
      (W.edges.toFinset.filter (fun e => e.2 = v)).card := Nat.add_right_cancel hb
  change ((arcSet R).filter _).card = ((arcSet R).filter _).card
  rw [hfilter, hfilter, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hs),
    Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hs), hbal v, he]

/-- Splicing an edge-disjoint closed walk into a trail preserves edge simplicity. -/
theorem splice_trails {V : Type*} {D : Digraph V} {x y v : V}
    (P : Walk D x v) (Q : Walk D v y) (C : Walk D v v)
    (hPQ : (P.edges ++ Q.edges).Nodup) (hC : C.edges.Nodup)
    (hdis : ∀ e ∈ C.edges, e ∉ P.edges ++ Q.edges) :
    ((P.comp C).comp Q).edges.Nodup := by
  rw [Walk.edges_comp, Walk.edges_comp]
  obtain ⟨hP, hQ, hPQ⟩ := List.nodup_append.mp hPQ
  apply (hP.append hC ?_).append hQ ?_
  · intro e heP heC
    exact hdis e heC (List.mem_append.mpr (Or.inl heP))
  · intro e hePC heQ
    rcases List.mem_append.mp hePC with heP | heC
    · exact hPQ e heP e heQ rfl
    · exact hdis e heC (List.mem_append.mpr (Or.inr heQ))

/-- A longest closed trail uses every outgoing arc at every place where it
can be split. This is the insertion step in the Euler-tour proof. -/
theorem longest_trail_exhausts_split {V : Type*} [Fintype V] (D : Digraph V)
    (hbal : Balanced D) {x : V} (W : Walk D x x) (hn : W.edges.Nodup)
    (hmax : ∀ z (P : Walk D x z), P.edges.Nodup → P.length ≤ W.length)
    {v : V} (P : Walk D x v) (Q : Walk D v x) (hPQ : W.edges = P.edges ++ Q.edges) :
    ∀ z, D v z → (v, z) ∈ W.edges := by
  intro z hvz
  by_contra hz
  let R : Digraph V := fun a b => D a b ∧ (a, b) ∉ W.edges
  obtain ⟨C, hC, hCm⟩ := longest_closed_trail R (residual_balanced D hbal W hn) v
  have hcpos : 1 ≤ C.length := by
    have h := hCm z (.cons .nil ⟨hvz, hz⟩) (by simp [Walk.edges])
    exact h
  let C' : Walk D v v := C.map id (fun _ _ h => h.1)
  have hce : C'.edges = C.edges := by simp [C']
  have hcl : C'.length = C.length := C.map_length id _
  have hdis : ∀ e ∈ C'.edges, e ∉ P.edges ++ Q.edges := by
    intro e he
    rw [hce] at he
    rw [← hPQ]
    exact (C.edge_mem he).2
  have hnd := splice_trails P Q C' (hPQ ▸ hn) (hce.symm ▸ hC) hdis
  have hm := hmax x ((P.comp C').comp Q) hnd
  have hlen := congrArg List.length hPQ
  simp only [List.length_append, Walk.edges_length] at hlen
  rw [Walk.length_comp, Walk.length_comp, hcl] at hm
  omega

/-- Euler's theorem for a finite strongly connected balanced digraph, proved
by a longest-trail argument and insertion of residual closed trails. -/
theorem directed_euler_tour {V : Type*} [Fintype V] (D : Digraph V)
    (hbal : Balanced D) (hD : StronglyConnected D) (x : V) :
    ∃ W : Walk D x x, W.edges.Nodup ∧ ∀ a b, D a b → (a, b) ∈ W.edges := by
  obtain ⟨W, hn, hmax⟩ := longest_closed_trail D hbal x
  have hvis : ∀ v, ∃ P : Walk D x v, ∃ Q : Walk D v x, W.edges = P.edges ++ Q.edges := by
    intro v
    have hreach := hD x v
    induction hreach with
    | refl => exact ⟨.nil, W, by simp [Walk.edges]⟩
    | @tail u v _ huv ih =>
      obtain ⟨P, Q, hPQ⟩ := ih
      have he := longest_trail_exhausts_split D hbal W hn hmax P Q hPQ v huv
      exact W.split_at_edge_head he
  refine ⟨W, hn, ?_⟩
  intro a b hab
  obtain ⟨P, Q, hPQ⟩ := hvis a
  exact longest_trail_exhausts_split D hbal W hn hmax P Q hPQ b hab

end DirectedCycles
