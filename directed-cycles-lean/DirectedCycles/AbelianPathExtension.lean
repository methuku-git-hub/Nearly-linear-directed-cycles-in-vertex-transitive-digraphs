import DirectedCycles.CayleyWords
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false
namespace DirectedCycles

theorem cayley_chain_translate {G : Type*} [Group G] (S : Set G) (b : G) (P : List G)
    (h : P.IsChain (CayleyDigraph S)) :
    (P.map (fun x => b*x)).IsChain (CayleyDigraph S) := by
  apply List.isChain_map_of_isChain _ _ h
  rintro x y ⟨a,ha,hy⟩
  exact ⟨a,ha,by rw [hy,mul_assoc]⟩

/-- Concatenating translates of a path through a subgroup visits exactly the
subgroup obtained by adjoining one element. All joins use that element in the
forward direction. -/
theorem abelian_path_extension {G : Type*} [CommGroup G] [Finite G]
    (H : Subgroup G) (S : Set G) (a : G) (P : List G)
    (hnd : P.Nodup) (hhead : P.head? = some 1)
    (hchain : P.IsChain (CayleyDigraph S)) (hmem : ∀ x, x ∈ P ↔ x ∈ H) :
    ∃ L : List G, L.Nodup ∧ L.head? = some 1 ∧
      L.IsChain (CayleyDigraph (insert a S)) ∧
      ∀ x, x ∈ L ↔ x ∈ H ⊔ Subgroup.zpowers a := by
  classical
  let q := QuotientGroup.mk' H
  have hP : P ≠ [] := by intro he; simp [he] at hhead
  let t := P.getLast hP
  have ht : t ∈ H := (hmem t).mp (List.getLast_mem hP)
  have hlast : P.getLast? = some t := List.getLast?_eq_some_getLast hP
  let y := t*a
  have hqt : q t = 1 := (QuotientGroup.eq_one_iff _).mpr ht
  have hqy : q y = q a := by simp only [y,map_mul,hqt,one_mul]
  have horder : orderOf (q a) ≠ 0 := (isOfFinOrder_of_finite (q a)).orderOf_pos.ne'
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero horder
  let F : Fin (m+1) → List G := fun i => P.map (fun x => y^i.val*x)
  have hFne : ∀ i, F i ≠ [] := by intro i; simpa [F] using hP
  have hFhead : ∀ i, (F i).head? = some (y^i.val) := by
    intro i; simp only [F,List.head?_map,hhead,Option.map_some,mul_one]
  have hFlast : ∀ i, (F i).getLast? = some (y^i.val*t) := by
    intro i; simp only [F,List.getLast?_map,hlast,Option.map_some]
  have hFq : ∀ i x, x ∈ F i → q x = (q a)^i.val := by
    intro i x hx
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
    have hqu : q u = 1 := (QuotientGroup.eq_one_iff _).mpr ((hmem u).mp hu)
    rw [map_mul,map_pow,hqy,hqu,mul_one]
  have hdis : ∀ i j, i ≠ j → (F i).Disjoint (F j) := by
    intro i j hij
    apply List.disjoint_left.mpr
    intro x hx hx'
    apply hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (hm.symm ▸ i.isLt) (hm.symm ▸ j.isLt)
      ((hFq i x hx).symm.trans (hFq j x hx'))
  refine ⟨(List.ofFn F).flatten,?_,?_,?_,?_⟩
  · apply List.nodup_flatten.mpr
    constructor
    · intro L hL
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hL
      exact hnd.map (fun _ _ h => mul_left_cancel h)
    · exact List.pairwise_ofFn.mpr (fun i j hij => hdis i j (ne_of_lt hij))
  · rw [List.ofFn_succ,List.flatten_cons,List.head?_append_of_ne_nil _ (hFne 0),hFhead]
    simp
  · apply (List.isChain_flatten (by simpa only [List.mem_ofFn] using not_exists.mpr hFne)).mpr
    constructor
    · intro L hL
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hL
      apply cayley_chain_translate _ _ _
      exact hchain.imp (fun _ _ ⟨s,hs,he⟩ => ⟨s,Set.mem_insert_of_mem a hs,he⟩)
    · apply List.isChain_ofFn.mpr
      intro i hi x hx z hz
      have hx' : x = y^i*t := by simpa only [hFlast,Option.mem_some_iff,eq_comm] using hx
      have hz' : z = y^(i+1) := by simpa only [hFhead,Option.mem_some_iff,eq_comm] using hz
      refine ⟨a,Set.mem_insert a S,?_⟩
      rw [hx',hz',pow_succ,mul_assoc]
  · intro x
    constructor
    · intro hx
      obtain ⟨L,hL,hx⟩ := List.mem_flatten.mp hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hL
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
      apply (H ⊔ Subgroup.zpowers a).mul_mem
      · apply (H ⊔ Subgroup.zpowers a).pow_mem
        exact (H ⊔ Subgroup.zpowers a).mul_mem (Subgroup.mem_sup_left ht)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
      · exact Subgroup.mem_sup_left ((hmem u).mp hu)
    · intro hx
      have hqx : q x ∈ Subgroup.zpowers (q a) := by
        obtain ⟨v,hv,w,hw,rfl⟩ := Subgroup.mem_sup.mp hx
        obtain ⟨z,rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        have hqv : q v = 1 := (QuotientGroup.eq_one_iff _).mpr hv
        rw [map_mul,map_zpow,hqv,one_mul]
        exact Subgroup.zpow_mem_zpowers _ _
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := q a)).mp hqx)
      have hi' : i < m+1 := by simpa only [hm,Finset.mem_range] using hi
      have hu : (y^i)⁻¹*x ∈ H := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q ((y^i)⁻¹*x) = 1
        rw [map_mul,map_inv,map_pow,hqy,← he,inv_mul_cancel]
      apply List.mem_flatten.mpr
      refine ⟨F ⟨i,hi'⟩,List.mem_ofFn.mpr ⟨⟨i,hi'⟩,rfl⟩,?_⟩
      apply List.mem_map.mpr
      exact ⟨(y^i)⁻¹*x,(hmem _).mpr hu,by simp only [mul_inv_cancel_left]⟩

end DirectedCycles
