import DirectedCycles.Paths

set_option autoImplicit false
namespace DirectedCycles

/-- A cyclic family of individually simple directed paths, with endpoints
included in every path. Different paths may intersect. -/
structure IsPathLoop {V : Type*} (D : Digraph V) {n : ℕ}
    (P : Fin n → List V) : Prop where
  nonempty : ∀ i, P i ≠ []
  nodup : ∀ i, (P i).Nodup
  chain : ∀ i, (P i).IsChain D
  join : ∀ i, (P i).getLast? = (P (finRotate n i)).head?

theorem rotate_iterate_ne_self {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (i : Fin n) : (finRotate n)^[k] i ≠ i := by
  let : NeZero n := ⟨by omega⟩
  intro he
  let j : Fin n := ⟨k, hkn⟩
  change (finRotate n)^[j.val] i = i at he
  rw [← finCycle_eq_finRotate_iterate, finCycle_apply] at he
  have hj : j = 0 := add_left_cancel (he.trans (add_zero i).symm)
  have hv := congrArg Fin.val hj
  change k = 0 at hv
  omega

/-- A cyclic family has a shortening with minimum total vertex count. -/
theorem minimal_path_loop {V : Type*} {D : Digraph V} {n : ℕ}
    (P : Fin n → List V) (hP : IsPathLoop D P) :
    ∃ T : Fin n → List V, IsPathLoop D T ∧ (∀ i, (T i).Sublist (P i)) ∧
      ∀ U : Fin n → List V, IsPathLoop D U → (∀ i, (U i).Sublist (P i)) →
        ∑ i, (T i).length ≤ ∑ i, (U i).length := by
  classical
  let admissible := fun T : Fin n → List V => IsPathLoop D T ∧ ∀ i, (T i).Sublist (P i)
  have hex : ∃ k : ℕ, ∃ T, admissible T ∧ ∑ i, (T i).length = k :=
    ⟨∑ i, (P i).length, P, ⟨hP, fun _ => List.Sublist.refl _⟩, rfl⟩
  obtain ⟨T, hT, hsum⟩ := Nat.find_spec hex
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro U hU hs
  rw [hsum]
  exact Nat.find_min' hex ⟨U, ⟨hU, hs⟩, rfl⟩

/-- Splicing two consecutive paths at a common vertex shortens both of them
and preserves all cyclic joins. -/
theorem splice_path_loop {V : Type*} {D : Digraph V} {n : ℕ}
    (P : Fin n → List V) (hP : IsPathLoop D P) (i : Fin n)
    (hne : finRotate n i ≠ i) (v : V) (a b c d : List V)
    (hi : P i = a ++ v :: b) (hj : P (finRotate n i) = c ++ v :: d) :
    ∃ U : Fin n → List V, IsPathLoop D U ∧ (∀ k, (U k).Sublist (P k)) ∧
      (U i).length = (a ++ [v]).length ∧
      (∀ k, k ≠ i → (U k).length ≤ (P k).length) := by
  classical
  let r := finRotate n
  let U : Fin n → List V := fun k =>
    if k = i then a ++ [v] else if k = r i then v :: d else P k
  have hu_i : U i = a ++ [v] := by simp [U]
  have hu_j : U (r i) = v :: d := by
    dsimp only [U]
    rw [ite_eq_right hne, ite_eq_left rfl]
  have hsub : ∀ k, (U k).Sublist (P k) := by
    intro k
    by_cases hki : k = i
    · subst k
      rw [hu_i, hi]
      exact (List.Sublist.refl a).append (List.Sublist.cons_cons _ (List.nil_sublist _))
    · by_cases hkj : k = r i
      · subst k
        rw [hu_j, hj]
        exact List.sublist_append_right _ _
      · simp [U, hki, hkj]
  have hstart : ∀ k, (U k).head? = if k = r i then some v else (P k).head? := by
    intro k
    by_cases hki : k = i
    · subst k
      rw [hu_i, ite_eq_right (Ne.symm hne), hi]
      cases a <;> simp
    · by_cases hkj : k = r i
      · subst k
        simp [hu_j]
      · simp [U, hki, hkj]
  have hend : ∀ k, (U k).getLast? = if k = i then some v else (P k).getLast? := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [hu_i]
    · by_cases hkj : k = r i
      · subst k
        rw [hu_j, ite_eq_right hne, hj]
        exact (List.getLast?_append_of_ne_nil _ (by simp)).symm
      · simp [U, hki, hkj]
  refine ⟨U, ?_, hsub, congrArg List.length hu_i, fun k _ => (hsub k).length_le⟩
  constructor
  · intro k
    by_cases hki : k = i
    · subst k; simp [hu_i]
    · by_cases hkj : k = r i
      · subst k; simp [hu_j]
      · simpa [U, hki, hkj] using hP.nonempty k
  · exact fun k => (hP.nodup k).sublist (hsub k)
  · intro k
    by_cases hki : k = i
    · subst k
      rw [hu_i]
      have hc := hP.chain i
      rw [hi] at hc
      exact (List.isChain_split.mp hc).1
    · by_cases hkj : k = r i
      · subst k
        rw [hu_j]
        have hc := hP.chain (r i)
        rw [hj] at hc
        exact hc.right_of_append
      · simpa [U, hki, hkj] using hP.chain k
  · intro k
    rw [hend, hstart]
    change (if k = i then some v else (P k).getLast?) =
      if r k = r i then some v else (P (r k)).head?
    by_cases hk : k = i
    · subst k; simp only [ite_true]
    · have hrk : r k ≠ r i := fun he => hk (r.injective he)
      simpa only [ite_eq_right hk, ite_eq_right hrk] using hP.join k

/-- In a minimizing family, a path with its last vertex removed is disjoint
from the entire next path. Otherwise splicing at the intersection is shorter. -/
theorem minimal_loop_disjoint_consecutive {V : Type*} {D : Digraph V} {n : ℕ}
    (P T : Fin n → List V) (hT : IsPathLoop D T)
    (hsub : ∀ i, (T i).Sublist (P i))
    (hmin : ∀ U : Fin n → List V, IsPathLoop D U →
      (∀ i, (U i).Sublist (P i)) → ∑ i, (T i).length ≤ ∑ i, (U i).length)
    (hr : ∀ i, finRotate n i ≠ i) :
    ∀ i, (T i).dropLast.Disjoint (T (finRotate n i)) := by
  intro i
  apply List.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨a, b, hab⟩ := List.mem_iff_append.mp hvi
  obtain ⟨c, d, hcd⟩ := List.mem_iff_append.mp hvj
  let t := (T i).getLast (hT.nonempty i)
  have hi : T i = a ++ v :: (b ++ [t]) := by
    calc T i = (T i).dropLast ++ [t] := (List.dropLast_append_getLast _).symm
         _ = a ++ v :: (b ++ [t]) := by rw [hab]; simp only [List.append_assoc, List.cons_append]
  obtain ⟨U, hU, hs, hlen, _⟩ := splice_path_loop T hT i (hr i) v a (b ++ [t]) c d hi hcd
  have hsmall : (U i).length < (T i).length := by
    rw [hlen, hi]
    simp only [List.length_append, List.length_cons]
    omega
  have hsum : ∑ k, (U k).length < ∑ k, (T k).length := by
    apply Finset.sum_lt_sum (fun k _ => (hs k).length_le)
    exact ⟨i, Finset.mem_univ _, hsmall⟩
  exact (not_lt_of_ge (hmin U hU (fun k => (hs k).trans (hsub k)))) hsum

/-- With at least four positions, the predecessor and successor of a position
are distinct and nonconsecutive. -/
theorem nonconsecutive_neighbours {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    (finRotate n).symm i ≠ finRotate n i ∧
    finRotate n i ≠ finRotate n ((finRotate n).symm i) ∧
    (finRotate n).symm i ≠ finRotate n (finRotate n i) := by
  let r := finRotate n
  have h1 := rotate_iterate_ne_self (n := n) (k := 1) (by omega) (by omega) i
  have h2 := rotate_iterate_ne_self (n := n) (k := 2) (by omega) (by omega) (r.symm i)
  have h3 := rotate_iterate_ne_self (n := n) (k := 3) (by omega) (by omega) (r.symm i)
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, r,
    Equiv.apply_symm_apply] at h1 h2 h3
  exact ⟨h2.symm, by simpa only [Equiv.apply_symm_apply] using h1, h3.symm⟩

/-- Disjointness of nonconsecutive original paths prevents a cyclic shortening
from collapsing any path to a single vertex. -/
theorem path_loop_dropLast_nonempty {V : Type*} {D : Digraph V} {n : ℕ}
    (hn : 4 ≤ n) (P T : Fin n → List V) (hT : IsPathLoop D T)
    (hsub : ∀ i, (T i).Sublist (P i))
    (hdis : ∀ i j, i ≠ j → j ≠ finRotate n i → i ≠ finRotate n j →
      (P i).Disjoint (P j)) :
    ∀ i, (T i).dropLast ≠ [] := by
  intro i hempty
  let r := finRotate n
  let v := (T i).getLast (hT.nonempty i)
  have hi : T i = [v] := by
    simpa [hempty] using (List.dropLast_append_getLast (hT.nonempty i)).symm
  have hp : (T (r.symm i)).getLast? = some v := by
    simpa only [r, Equiv.apply_symm_apply, hi, List.head?_cons] using hT.join (r.symm i)
  have hs : (T (r i)).head? = some v := by
    simpa only [hi, List.getLast?_singleton] using (hT.join i).symm
  have hvp : v ∈ T (r.symm i) := List.mem_of_mem_getLast? hp
  have hvs : v ∈ T (r i) := List.mem_of_mem_head? hs
  obtain ⟨hne, hn₁, hn₂⟩ := nonconsecutive_neighbours hn i
  exact List.disjoint_left.mp (hdis _ _ hne hn₁ hn₂)
    ((hsub _).subset hvp) ((hsub _).subset hvs)

/-- The minimization argument produces disjoint half-open paths and hence a
simple cycle of length at least the number of paths. -/
theorem shortening_path_loop {V : Type*} {D : Digraph V} {n : ℕ}
    (hn : 4 ≤ n) (P : Fin n → List V) (hP : IsPathLoop D P)
    (hdis : ∀ i j, i ≠ j → j ≠ finRotate n i → i ≠ finRotate n j →
      (P i).Disjoint (P j)) :
    ∃ C : Cycle D, n ≤ C.length := by
  obtain ⟨T, hT, hs, hmin⟩ := minimal_path_loop P hP
  have hr : ∀ i, finRotate n i ≠ i := by
    intro i
    simpa only [Function.iterate_one] using
      rotate_iterate_ne_self (n := n) (k := 1) (by omega) (by omega) i
  have hc := minimal_loop_disjoint_consecutive P T hT hs hmin hr
  have hne := path_loop_dropLast_nonempty hn P T hT hs hdis
  have hall : ∀ i j, i ≠ j → (T i).dropLast.Disjoint (T j).dropLast := by
    intro i j hij
    apply List.disjoint_left.mpr
    intro v hvi hvj
    by_cases hj : j = finRotate n i
    · subst j
      exact List.disjoint_left.mp (hc i) hvi ((List.dropLast_sublist _).subset hvj)
    · by_cases hi : i = finRotate n j
      · subst i
        exact List.disjoint_left.mp (hc j) hvj ((List.dropLast_sublist _).subset hvi)
      · exact List.disjoint_left.mp (hdis i j hij hj hi)
          ((hs i).subset ((List.dropLast_sublist _).subset hvi))
          ((hs j).subset ((List.dropLast_sublist _).subset hvj))
  have hhead : ∀ i, (T i).dropLast.head? = (T i).head? := by
    intro i
    conv_rhs => rw [← List.dropLast_append_getLast (hT.nonempty i)]
    exact (List.head?_append_of_ne_nil _ (hne i)).symm
  have hjoin : ∀ i, ∀ u ∈ (T i).dropLast.getLast?,
      ∀ v ∈ (T (finRotate n i)).dropLast.head?, D u v := by
    intro i u hu v hv
    rw [hhead, ← hT.join i, List.getLast?_eq_some_getLast (hT.nonempty i)] at hv
    have hv' : v = (T i).getLast (hT.nonempty i) := by
      simpa only [Option.mem_some_iff, eq_comm] using hv
    subst v
    have hp := hT.chain i
    conv at hp => rhs; rw [← List.dropLast_append_getLast (hT.nonempty i)]
    exact (List.isChain_append.mp hp).2.2 u hu _ (by simp)
  obtain ⟨C, _, hC, _⟩ := cycle_of_disjoint_segments (by omega : 2 ≤ n)
    (fun i => (T i).dropLast) hne
    (fun i => (hT.nodup i).sublist (List.dropLast_sublist _)) hall
    (fun i => (hT.chain i).dropLast) hjoin
  exact ⟨C, hC⟩

/-- An edge belongs to the union of the specified paths when its ordered pair
occurs consecutively in one of them. -/
def PathUnion {V : Type*} {n : ℕ} (P : Fin n → List V) : Digraph V :=
  fun x y => ∃ i, [x, y] <:+: P i

/-- Manuscript Lemma 4.4, with the additional explicit guarantee that every
edge of the resulting cycle occurs in one of the original paths. -/
theorem shortening_consecutive_intersections {V : Type*} {D : Digraph V} {n : ℕ}
    (hn : 4 ≤ n) (P : Fin n → List V) (hP : IsPathLoop D P)
    (hdis : ∀ i j, i ≠ j → j ≠ finRotate n i → i ≠ finRotate n j →
      (P i).Disjoint (P j)) :
    ∃ C : Cycle D, n ≤ C.length ∧ ∀ k,
      ∃ i, [C.vertex k, C.vertex (finRotate C.length k)] <:+: P i := by
  have hU : IsPathLoop (PathUnion P) P := by
    refine ⟨hP.nonempty, hP.nodup, ?_, hP.join⟩
    intro i
    exact (List.isChain_isInfix (P i)).imp (fun x y h => ⟨i, h⟩)
  obtain ⟨C, hC⟩ := shortening_path_loop hn P hU hdis
  have hmap : ∀ x y, PathUnion P x y → D x y := by
    intro x y h
    obtain ⟨i, hi⟩ := h
    exact List.isChain_pair.mp ((hP.chain i).infix hi)
  exact ⟨C.map (Function.Embedding.refl _) hmap, hC, C.arc⟩

end DirectedCycles
