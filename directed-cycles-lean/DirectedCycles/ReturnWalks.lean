module

public import DirectedCycles.ReturnVoltages

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The two directed trees and their actual voltage equations. The outward
tree has been normalized by changing orbit representatives. -/
structure ReturnSpine {G I : Type*} [Group G] [Fintype I]
    (S : I → I → Set G) (root : I) where
  out : PartialOutBranching (fun i j => (S i j).Nonempty) root Finset.univ
  inward : PartialOutBranching (fun i j => (S j i).Nonempty) root Finset.univ
  voltage : I → G
  root_voltage : voltage root = 1
  out_label : ∀ i j, out.arc i j → 1 ∈ S i j
  in_label : ∀ i j, inward.arc j i → voltage i * (voltage j)⁻¹ ∈ S i j

namespace ReturnSpine
variable {G I : Type*} [Group G] [Fintype I] {S : I → I → Set G} {root : I}

noncomputable def outPath (R : ReturnSpine S root) (i : I) := R.out.path i (Finset.mem_univ i)
noncomputable def inPath (R : ReturnSpine S root) (i : I) :=
  (R.inward.path i (Finset.mem_univ i)).reverse

noncomputable def walkVertices (R : ReturnSpine S root) (x : G) (i j : I) (s : G) : List (G × I) :=
  (R.outPath i).vertices.map (fun k => (x,k)) ++
  (R.inPath j).vertices.map (fun k => (x*s*R.voltage j*(R.voltage k)⁻¹,k))

theorem walk_head (R : ReturnSpine S root) (x : G) (i j : I) (s : G) :
    (R.walkVertices x i j s).head? = some (x,root) := by
  rw [walkVertices,List.head?_append_of_ne_nil _ (by simpa using (R.outPath i).nonempty)]
  simp only [List.head?_map,(R.outPath i).head,Option.map_some]

theorem walk_last (R : ReturnSpine S root) (x : G) (i j : I) (s : G) :
    (R.walkVertices x i j s).getLast? = some (x*s*R.voltage j,root) := by
  rw [walkVertices,List.getLast?_append_of_ne_nil _ (by simpa using (R.inPath j).nonempty)]
  simp only [List.getLast?_map,(R.inPath j).last,Option.map_some,R.root_voltage,inv_one,mul_one]

theorem walk_chain (R : ReturnSpine S root) (x : G) (i j : I) (s : G) (hs : s ∈ S i j) :
    (R.walkVertices x i j s).IsChain (VoltageDigraph S) := by
  apply List.IsChain.append
  · rw [List.isChain_map]
    apply (R.outPath i).chain.imp
    intro a b hab
    exact ⟨1,R.out_label a b hab,by simp⟩
  · rw [List.isChain_map]
    apply (R.inPath j).chain.imp
    intro a b hab
    refine ⟨R.voltage a*(R.voltage b)⁻¹,R.in_label a b hab,?_⟩
    change x*s*R.voltage j*(R.voltage b)⁻¹ =
      x*s*R.voltage j*(R.voltage a)⁻¹*(R.voltage a*(R.voltage b)⁻¹)
    group
  · intro a ha b hb
    have ha' : a = (x,i) := by
      simpa only [List.getLast?_map,(R.outPath i).last,Option.map_some,Option.mem_some_iff,
        eq_comm] using ha
    have hb' : b = (x*s,j) := by
      simpa only [List.head?_map,(R.inPath j).head,Option.map_some,mul_inv_cancel_right,
        Option.mem_some_iff,eq_comm] using hb
    subst a; subst b
    exact ⟨s,hs,rfl⟩

theorem walk_length (R : ReturnSpine S root) (x : G) (i j : I) (s : G) :
    (R.walkVertices x i j s).length =
      (R.outPath i).vertices.length + (R.inPath j).vertices.length := by
  simp only [walkVertices,List.length_append,List.length_map]

theorem walk_occurrence (R : ReturnSpine S root) (x : G) (i j : I) (s : G)
    (z : G × I) (hz : z ∈ R.walkVertices x i j s) :
    z.1 = x ∨ z.1 = x*s*R.voltage j*(R.voltage z.2)⁻¹ := by
  rcases List.mem_append.mp hz with h | h
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp h
    exact Or.inl rfl
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp h
    exact Or.inr rfl

/-- The complete collision alternatives, including the two mixed cases. -/
theorem walk_collision (R : ReturnSpine S root) (x x' : G) (i j i' j' : I) (s s' : G)
    (z : G × I) (hz : z ∈ R.walkVertices x i j s) (hz' : z ∈ R.walkVertices x' i' j' s') :
    x = x' ∨ x*s*R.voltage j = x'*s'*R.voltage j' ∨
      x'*s'*R.voltage j' = x*R.voltage z.2 ∨ x*s*R.voltage j = x'*R.voltage z.2 := by
  rcases R.walk_occurrence x i j s z hz with h | h <;>
    rcases R.walk_occurrence x' i' j' s' z hz' with h' | h'
  · exact Or.inl (h.symm.trans h')
  · exact Or.inr (Or.inr (Or.inl (by
      have he := h'.symm.trans h
      exact (mul_inv_eq_iff_eq_mul).mp he)))
  · exact Or.inr (Or.inr (Or.inr (by
      have he := h.symm.trans h'
      exact (mul_inv_eq_iff_eq_mul).mp he)))
  · exact Or.inr (Or.inl (mul_right_cancel (h.symm.trans h')))

theorem products_generate (R : ReturnSpine S root) (hsc : StronglyConnected (VoltageDigraph S)) :
    Subgroup.closure {g : G | ∃ i j s, s ∈ S i j ∧ g = s * R.voltage j} = ⊤ :=
  return_products_generate R.out S R.voltage R.root_voltage R.out_label hsc

end ReturnSpine
end DirectedCycles
