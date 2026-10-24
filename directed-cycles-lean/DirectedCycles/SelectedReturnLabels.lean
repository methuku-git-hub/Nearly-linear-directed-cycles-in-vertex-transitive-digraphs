import DirectedCycles.ShortestReturnWalks

set_option autoImplicit false
namespace DirectedCycles
namespace ReturnSpine
variable {G H I : Type*} [Group G] [Group H] [Fintype I] {S : I → I → Set G} {root : I}

/-- Select one quotient-simple return walk for each nonidentity quotient
product. The selected products still generate the quotient. -/
theorem select_return_labels (R : ReturnSpine S root) (q : G →* H)
    (hq : Function.Surjective q) (hsc : StronglyConnected (VoltageDigraph S)) :
    ∃ T : Set G,
      (∀ s ∈ T, q s ≠ 1) ∧ Subgroup.closure (q '' T) = ⊤ ∧
      ∀ s ∈ T, ∃ i j u, u ∈ S i j ∧ s = u*R.voltage j ∧
        ((R.walkVertices 1 i j u).map (fun z => (q z.1,z.2))).Nodup := by
  classical
  let A : Set G := {g | ∃ i j u, u ∈ S i j ∧ g = u*R.voltage j}
  let J := {y : H // y ≠ 1 ∧ y ∈ q '' A}
  have hchoices : ∀ y : J, ∃ i j u, u ∈ S i j ∧ q (u*R.voltage j) = y.val ∧
      ((R.walkVertices 1 i j u).map (fun z => (q z.1,z.2))).Nodup := by
    intro y
    obtain ⟨g,⟨i,j,u,hu,rfl⟩,hgy⟩ := y.property.2
    obtain ⟨i',j',u',hu',he,hnd⟩ := R.exists_simple_quotient_return q i j u hu
      (hgy ▸ y.property.1)
    exact ⟨i',j',u',hu',he.trans hgy,hnd⟩
  choose i j u hu he hnd using hchoices
  let f := fun y : J => u y*R.voltage (j y)
  let T := Set.range f
  refine ⟨T,?_,?_,?_⟩
  · rintro s ⟨y,rfl⟩
    exact (he y) ▸ y.property.1
  · have hA : Subgroup.closure (q '' A) = ⊤ := by
      rw [← MonoidHom.map_closure,R.products_generate hsc,Subgroup.map_top_of_surjective _ hq]
    have hle : Subgroup.closure (q '' A) ≤ Subgroup.closure (q '' T) := by
      rw [Subgroup.closure_le]
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact Subgroup.one_mem _
      · let z : J := ⟨y,hy1,hy⟩
        exact Subgroup.subset_closure ⟨f z,⟨z,rfl⟩,he z⟩
    rw [hA] at hle
    exact top_unique hle
  · rintro s ⟨y,rfl⟩
    exact ⟨i y,j y,u y,hu y,rfl,hnd y⟩

end ReturnSpine
end DirectedCycles
