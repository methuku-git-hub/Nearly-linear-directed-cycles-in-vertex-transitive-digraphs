import DirectedCycles.LocalGroupProducts

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Existential split witnesses are safe as a theorem, while the inductive
constructor retains its explicit function witnesses for kernel recursion. -/
theorem Product.of_splits {l : List G} {x : G} (hlen : 2 ≤ l.length)
    (h : ∀ a b : List G, l = a++b → a ≠ [] → b ≠ [] →
      ∃ u v : G, L.Product a u ∧ L.Product b v ∧ L.mulRel u v x) : L.Product l x := by
  classical
  have hc : ∀ a b : List G, ∃ u v : G, l = a++b → a ≠ [] → b ≠ [] →
      L.Product a u ∧ L.Product b v ∧ L.mulRel u v x := by
    intro a b
    by_cases he : l = a++b ∧ a ≠ [] ∧ b ≠ []
    · obtain ⟨u,v,hu,hv,hm⟩ := h a b he.1 he.2.1 he.2.2
      exact ⟨u,v,fun _ _ _ => ⟨hu,hv,hm⟩⟩
    · exact ⟨L.one,L.one,fun h1 h2 h3 => (he ⟨h1,h2,h3⟩).elim⟩
  choose u v huv using hc
  exact Product.splits hlen u v (fun a b he ha hb => (huv a b he ha hb).1)
    (fun a b he ha hb => (huv a b he ha hb).2.1)
    (fun a b he ha hb => (huv a b he ha hb).2.2)

/-- There are only finitely many contiguous split obligations at each fixed
word length. This formulation permits direct ultraproduct transfer. -/
theorem product_iff_finite_splits {l : List G} {x : G} (hlen : 2 ≤ l.length) :
    L.Product l x ↔ ∀ k : Fin (l.length+1), 0 < k.val → k.val < l.length →
      ∃ u v : G, L.Product (l.take k.val) u ∧ L.Product (l.drop k.val) v ∧ L.mulRel u v x := by
  constructor
  · intro h k hk hk'
    apply h.split L (List.take_append_drop k.val l).symm
    · intro he
      have hh := congrArg List.length he
      simp only [List.length_take,List.length_nil] at hh
      omega
    · intro he
      have hh := congrArg List.length he
      simp only [List.length_drop,List.length_nil] at hh
      omega
  · intro h
    apply Product.of_splits L hlen
    intro a b he ha hb
    have hal : 0 < a.length := List.length_pos_iff.mpr ha
    have hbl : 0 < b.length := List.length_pos_iff.mpr hb
    have hlen' : l.length = a.length+b.length := by simp only [he,List.length_append]
    obtain ⟨u,v,hu,hv,hm⟩ := h ⟨a.length,by omega⟩ hal (by change a.length < l.length; omega)
    exact ⟨u,v,by simpa only [he,List.take_left] using hu,
      by simpa only [he,List.drop_left] using hv,hm⟩

/-- The finite-split characterization, stated before mapping the word. -/
theorem mapped_product_iff_finite_splits {J : Type*} (f : J → G) {l : List J} {x : G}
    (hlen : 2 ≤ l.length) :
    L.Product (l.map f) x ↔ ∀ k : Fin (l.length+1), 0 < k.val → k.val < l.length →
      ∃ u v : G, L.Product ((l.take k.val).map f) u ∧
        L.Product ((l.drop k.val).map f) v ∧ L.mulRel u v x := by
  constructor
  · intro h k hk hk'
    have hm := (product_iff_finite_splits L (l := l.map f) (x := x) (by simpa using hlen)).1 h
    obtain ⟨u,v,hu,hv,hmul⟩ := hm ⟨k.val,by simpa using k.isLt⟩ hk (by simpa using hk')
    exact ⟨u,v,by simpa only [List.map_take] using hu,
      by simpa only [List.map_drop] using hv,hmul⟩
  · intro h
    apply (product_iff_finite_splits L (l := l.map f) (x := x) (by simpa using hlen)).2
    intro k hk hk'
    obtain ⟨u,v,hu,hv,hmul⟩ := h ⟨k.val,by simpa using k.isLt⟩ hk (by simpa using hk')
    exact ⟨u,v,by simpa only [List.map_take] using hu,
      by simpa only [List.map_drop] using hv,hmul⟩
end LocalGroupAlgebra
end DirectedCycles
