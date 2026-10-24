import DirectedCycles.Paths

set_option autoImplicit false
namespace DirectedCycles

/-- A rooted outward branching on a specified finite vertex set. Unique
incoming edges and root reachability encode the tree property explicitly. -/
structure PartialOutBranching {V : Type*} (D : Digraph V) (root : V) (U : Finset V) where
  arc : Digraph V
  subgraph : ∀ x y, arc x y → D x y
  support : ∀ x y, arc x y → x ∈ U ∧ y ∈ U
  root_mem : root ∈ U
  root_no_in : ∀ x, ¬ arc x root
  unique_in : ∀ v x y, arc x v → arc y v → x = y
  reachable : ∀ v ∈ U, Reachable arc root v

theorem reachable_leaving_set {V : Type*} {D : Digraph V} (U : Set V)
    {x y : V} (hx : x ∈ U) (hy : y ∉ U) (h : Reachable D x y) :
    ∃ u ∈ U, ∃ v ∉ U, D u v := by
  have hh : ∀ {y : V}, Reachable D x y → y ∉ U → ∃ u ∈ U, ∃ v ∉ U, D u v := by
    intro y hr
    induction hr with
    | refl => exact fun hn => (hn hx).elim
    | @tail z y hr hzy ih =>
      intro hny
      by_cases hz : z ∈ U
      · exact ⟨z,hz,y,hny,hzy⟩
      · exact ih hz
  exact hh h hy

namespace PartialOutBranching
variable {V : Type*} {D : Digraph V} {root : V} {U : Finset V}

def changeGraph (B : PartialOutBranching D root U) (E : Digraph V)
    (h : ∀ x y, B.arc x y → E x y) : PartialOutBranching E root U where
  arc := B.arc
  subgraph := h
  support := B.support
  root_mem := B.root_mem
  root_no_in := B.root_no_in
  unique_in := B.unique_in
  reachable := B.reachable

/-- Adding one edge from the existing tree to a new vertex preserves every
branching invariant and every previously selected arc. -/
def extend [DecidableEq V] (B : PartialOutBranching D root U)
    (x y : V) (hx : x ∈ U) (hy : y ∉ U) (hxy : D x y) :
    PartialOutBranching D root (insert y U) where
  arc u v := B.arc u v ∨ (u = x ∧ v = y)
  subgraph := by
    intro u v huv
    rcases huv with h | ⟨rfl,rfl⟩
    · exact B.subgraph u v h
    · exact hxy
  support := by
    intro u v huv
    rcases huv with h | ⟨rfl,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (B.support u v h).1,Finset.mem_insert_of_mem (B.support u v h).2⟩
    · exact ⟨Finset.mem_insert_of_mem hx,Finset.mem_insert_self _ _⟩
  root_mem := Finset.mem_insert_of_mem B.root_mem
  root_no_in := by
    intro u hu
    rcases hu with h | ⟨_,hroot⟩
    · exact B.root_no_in u h
    · exact hy (hroot ▸ B.root_mem)
  unique_in := by
    intro v u w hu hw
    rcases hu with hu | ⟨rfl,rfl⟩
    · rcases hw with hw | ⟨rfl,rfl⟩
      · exact B.unique_in v u w hu hw
      · exact (hy (B.support _ _ hu).2).elim
    · rcases hw with hw | ⟨he,_⟩
      · exact (hy (B.support _ _ hw).2).elim
      · exact he.symm
  reachable := by
    intro v hv
    have hmap : ∀ z ∈ U, Reachable (fun u w => B.arc u w ∨ (u=x ∧ w=y)) root z := by
      intro z hz
      exact reachable_map (fun v : V => v) (fun u w (h : B.arc u w) => Or.inl h) (B.reachable z hz)
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (hmap x hx).tail (Or.inr ⟨rfl,rfl⟩)
    · exact hmap v hv

theorem extends_to_spanning [Fintype V] [DecidableEq V]
    (B : PartialOutBranching D root U) (hsc : StronglyConnected D) :
    ∃ C : PartialOutBranching D root Finset.univ, ∀ x y, B.arc x y → C.arc x y := by
  have hall : ∀ m : ℕ, ∀ U : Finset V, (Finset.univ \ U).card = m →
      ∀ B : PartialOutBranching D root U,
      ∃ C : PartialOutBranching D root Finset.univ, ∀ x y, B.arc x y → C.arc x y := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro U hm B
      by_cases hU : U = Finset.univ
      · subst U
        exact ⟨B,fun _ _ h => h⟩
      · obtain ⟨y,hy⟩ : ∃ y : V, y ∉ U := by
          by_contra he
          push Not at he
          exact hU (Finset.eq_univ_of_forall he)
        obtain ⟨x,hx,z,hz,hxz⟩ := reachable_leaving_set (U : Set V) B.root_mem hy (hsc root y)
        let B' := B.extend x z hx hz hxz
        have hlt : (Finset.univ \ insert z U).card < m := by
          rw [← hm,Finset.card_sdiff,Finset.card_sdiff,Finset.inter_univ,Finset.inter_univ,
            Finset.card_insert_of_notMem hz]
          have hu : U.card < Fintype.card V := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hU)
          simp only [Finset.card_univ]
          omega
        obtain ⟨C,hC⟩ := ih _ hlt (insert z U) rfl B'
        exact ⟨C,fun u v huv => hC u v (Or.inl huv)⟩
  exact hall _ U rfl B

end PartialOutBranching
end DirectedCycles
