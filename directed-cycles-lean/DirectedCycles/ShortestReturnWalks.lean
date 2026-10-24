import DirectedCycles.ReturnWalks

set_option autoImplicit false
namespace DirectedCycles
namespace ReturnSpine
variable {G H I : Type*} [Group G] [Group H] [Fintype I] {S : I → I → Set G} {root : I}

theorem outPath_length_le_of_mem (R : ReturnSpine S root) {i k : I}
    (hk : k ∈ (R.outPath i).vertices) :
    (R.outPath k).vertices.length ≤ (R.outPath i).vertices.length :=
  (R.out.path_prefix (Finset.mem_univ i) (Finset.mem_univ k) hk).length_le

theorem inPath_length_le_of_mem (R : ReturnSpine S root) {j k : I}
    (hk : k ∈ (R.inPath j).vertices) :
    (R.inPath k).vertices.length ≤ (R.inPath j).vertices.length := by
  change k ∈ (R.inward.path j (Finset.mem_univ j)).vertices.reverse at hk
  have hh := (R.inward.path_prefix (Finset.mem_univ j) (Finset.mem_univ k)
    (List.mem_reverse.mp hk)).length_le
  simpa only [inPath,SimplePath.reverse,List.length_reverse] using hh

/-- The shortest return walk representing a nonidentity quotient element
has no repeated quotient vertex. The competitor is the return walk on the
outward-tree arc entering the repeated orbit. -/
theorem minimal_walk_quotient_nodup (R : ReturnSpine S root) (q : G →* H)
    (i j : I) (s : G) (hne : q (s*R.voltage j) ≠ 1)
    (hmin : ∀ i' j' s', s' ∈ S i' j' → q (s'*R.voltage j') = q (s*R.voltage j) →
      (R.walkVertices 1 i j s).length ≤ (R.walkVertices 1 i' j' s').length) :
    ((R.walkVertices 1 i j s).map (fun z => (q z.1,z.2))).Nodup := by
  simp only [walkVertices,List.map_append,List.map_map]
  apply List.nodup_append.mpr
  refine ⟨?_,?_,?_⟩
  · exact (R.outPath i).nodup.map (fun a b he => congrArg Prod.snd he)
  · exact (R.inPath j).nodup.map (fun a b he => congrArg Prod.snd he)
  · intro u hu v hv he
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hu
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
    have hkl : k = l := congrArg Prod.snd he
    subst l
    have hprod : q (s*R.voltage j) = q (R.voltage k) := by
      have hh := congrArg Prod.fst he
      simp only [Function.comp_apply,one_mul,map_one,map_mul,map_inv] at hh
      rw [map_mul]
      exact (mul_inv_eq_one.mp hh.symm)
    have hkr : k ≠ root := by
      intro he
      exact hne (hprod.trans (by rw [he,R.root_voltage,map_one]))
    obtain ⟨p,hpk⟩ := R.out.incoming (Finset.mem_univ k) hkr
    have hshort := hmin p k 1 (R.out_label p k hpk)
      (by simpa only [one_mul] using hprod.symm)
    have hP := R.out.path_append_of_arc (Finset.mem_univ p) (Finset.mem_univ k) hpk
    have hlen := congrArg List.length hP
    change (R.outPath k).vertices.length = ((R.outPath p).vertices ++ [k]).length at hlen
    simp only [List.length_append,List.length_singleton] at hlen
    have hleP := R.outPath_length_le_of_mem hk
    have hleZ := R.inPath_length_le_of_mem hl
    rw [R.walk_length,R.walk_length] at hshort
    omega

/-- A shortest representative exists for every represented nonidentity
quotient element; its simplicity is a conclusion, not a premise. -/
theorem exists_simple_quotient_return (R : ReturnSpine S root) (q : G →* H)
    (i j : I) (s : G) (hs : s ∈ S i j) (hne : q (s*R.voltage j) ≠ 1) :
    ∃ i' j' s', s' ∈ S i' j' ∧ q (s'*R.voltage j') = q (s*R.voltage j) ∧
      ((R.walkVertices 1 i' j' s').map (fun z => (q z.1,z.2))).Nodup := by
  classical
  let P : ℕ → Prop := fun n => ∃ i' j' s', s' ∈ S i' j' ∧
    q (s'*R.voltage j') = q (s*R.voltage j) ∧ (R.walkVertices 1 i' j' s').length = n
  have hex : ∃ n, P n := ⟨_,i,j,s,hs,rfl,rfl⟩
  obtain ⟨i',j',s',hs',hq',hlen⟩ := Nat.find_spec hex
  refine ⟨i',j',s',hs',hq',R.minimal_walk_quotient_nodup q i' j' s' (hq' ▸ hne) ?_⟩
  intro i'' j'' s'' hs'' hq''
  rw [hlen]
  exact Nat.find_min' hex ⟨i'',j'',s'',hs'',hq''.trans hq',rfl⟩

end ReturnSpine

/-- Translates of a quotient-simple walk by distinct elements in one
quotient fibre are disjoint, including both endpoints. -/
theorem quotient_simple_translates_disjoint {G H I : Type*} [Group G] [Group H]
    (q : G →* H) (L : List (G × I))
    (hnd : (L.map (fun z => (q z.1,z.2))).Nodup)
    (x y : G) (hq : q x = q y) (hne : x ≠ y) :
    (L.map (fun z => (x*z.1,z.2))).Disjoint (L.map (fun z => (y*z.1,z.2))) := by
  apply List.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨u,hu,hu'⟩ := List.mem_map.mp hz
  obtain ⟨v,hv,hv'⟩ := List.mem_map.mp hz'
  have he : (x*u.1,u.2) = (y*v.1,v.2) := hu'.trans hv'.symm
  have huv : (q u.1,u.2) = (q v.1,v.2) := by
    apply Prod.ext
    · have hh := congrArg (fun z : G × I => q z.1) he
      simp only [map_mul] at hh
      rw [hq] at hh
      exact mul_left_cancel hh
    · have hh := congrArg (fun z : G × I => z.2) he
      exact hh
  have heq : u = v := (List.nodup_map_iff_inj_on (List.Nodup.of_map _ hnd)).mp hnd u hu v hv huv
  subst v
  exact hne (mul_right_cancel (congrArg Prod.fst he))

end DirectedCycles
