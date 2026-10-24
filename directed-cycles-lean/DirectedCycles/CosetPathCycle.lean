import DirectedCycles.AbelianPathExtension
import DirectedCycles.PathPrefixes

set_option autoImplicit false
namespace DirectedCycles

/-- A cyclic quotient and a Hamiltonian subgroup path give a simple cycle
containing all but its last coset completely. Those complete cosets occur
before the final vertex. -/
theorem cycle_from_cyclic_quotient {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (S : Set G) (a : G) (ha : a ∈ S)
    (hm : 2 ≤ orderOf (QuotientGroup.mk' H a))
    (P : List G) (hnd : P.Nodup) (hh : P.head? = some 1)
    (hc : P.IsChain (CayleyDigraph S)) (hmem : ∀ x, x ∈ P ↔ x ∈ H) :
    ∃ (C : Cycle (CayleyDigraph S)) (y : G),
      QuotientGroup.mk' H y = QuotientGroup.mk' H a ∧
      (orderOf (QuotientGroup.mk' H a)-1)*Nat.card H+1 ≤ C.length ∧
      ∀ i : ℕ, i < orderOf (QuotientGroup.mk' H a)-1 → ∀ u : H,
        y^i*u.val ∈ (List.ofFn C.vertex).dropLast := by
  classical
  let q := QuotientGroup.mk' H
  change 2 ≤ orderOf (q a) at hm
  obtain ⟨n,hn⟩ : ∃ n, orderOf (q a) = n+2 := ⟨orderOf (q a)-2,by omega⟩
  have hP : P ≠ [] := by intro he; simp [he] at hh
  let t := P.getLast hP
  have ht : t ∈ H := (hmem t).mp (List.getLast_mem hP)
  have hlast : P.getLast? = some t := List.getLast?_eq_some_getLast hP
  let y := t*a
  have hqy : q y = q a := by
    have hqt : q t = 1 := (QuotientGroup.eq_one_iff _).mpr ht
    simp only [y,map_mul,hqt,one_mul]
  have hpow : (q a)^(n+1) = (q a)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ,← hn,pow_orderOf_eq_one]
  let w := (y^(n+1))⁻¹*a⁻¹
  have hw : w ∈ P := by
    apply (hmem w).mpr
    apply (QuotientGroup.eq_one_iff _).mp
    change q w = 1
    simp only [w,map_mul,map_inv,map_pow,hqy,hpow,inv_inv,mul_inv_cancel]
  obtain ⟨R,hRP,hRne,hRnd,hRc,hRh,hRl⟩ := prefix_through_vertex P hnd hc hh hw
  let F : Fin (n+2) → List G := fun i =>
    (if i.val = n+1 then R else P).map (fun x => y^i.val*x)
  have hFsub : ∀ i, F i <+: P.map (fun x => y^i.val*x) := by
    intro i
    dsimp only [F]
    split_ifs with hi
    · exact hRP.map _
    · exact ⟨[],by simp⟩
  have hFnd : ∀ i, (F i).Nodup := by
    intro i
    exact (hnd.map (fun _ _ h => mul_left_cancel h)).sublist (hFsub i).sublist
  have hFhead : ∀ i, (F i).head? = some (y^i.val) := by
    intro i
    dsimp only [F]
    split_ifs <;> simp only [List.head?_map,hRh,hh,Option.map_some,mul_one]
  have hFne : ∀ i, F i ≠ [] := by
    intro i he
    have hi := hFhead i
    simp [he] at hi
  have hFc : ∀ i, (F i).IsChain (CayleyDigraph S) := by
    intro i
    exact (cayley_chain_translate S _ P hc).prefix (hFsub i)
  have hFlast : ∀ i, i.val < n+1 → (F i).getLast? = some (y^i.val*t) := by
    intro i hi
    have he : ¬ i.val = n+1 := by omega
    simp only [F,he,ite_false,List.getLast?_map,hlast,Option.map_some]
  have hFend : (F (Fin.last (n+1))).getLast? = some a⁻¹ := by
    simp only [F,Fin.val_last,ite_true,List.getLast?_map,hRl,Option.map_some,w,
      mul_inv_cancel_left]
  have hFq : ∀ i x, x ∈ F i → q x = (q a)^i.val := by
    intro i x hx
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ((hFsub i).subset hx)
    have hqu : q u = 1 := (QuotientGroup.eq_one_iff _).mpr ((hmem u).mp hu)
    rw [map_mul,map_pow,hqy,hqu,mul_one]
  have hdis : ∀ i j, i ≠ j → (F i).Disjoint (F j) := by
    intro i j hij
    apply List.disjoint_left.mpr
    intro x hx hx'
    apply hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (hn.symm ▸ i.isLt) (hn.symm ▸ j.isLt)
      ((hFq i x hx).symm.trans (hFq j x hx'))
  have hjoin : ∀ i, ∀ x ∈ (F i).getLast?, ∀ z ∈ (F (finRotate (n+2) i)).head?,
      CayleyDigraph S x z := by
    intro i x hx z hz
    by_cases hi : i.val < n+1
    · have hnxt : (finRotate (n+2) i).val = i.val+1 := by
        rw [finRotate_apply]
        simp only [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1 < n+2 by omega),
          Nat.mod_eq_of_lt (show i.val+1 < n+2 by omega)]
      have hx' : x = y^i.val*t := by simpa only [hFlast i hi,Option.mem_some_iff,eq_comm] using hx
      have hz' : z = y^(i.val+1) := by simpa only [hFhead,hnxt,Option.mem_some_iff,eq_comm] using hz
      exact ⟨a,ha,by rw [hx',hz',pow_succ,mul_assoc]⟩
    · have hi' : i = Fin.last (n+1) := Fin.ext (show i.val = n+1 by omega)
      subst i
      have hx' : x = a⁻¹ := by simpa only [hFend,Option.mem_some_iff,eq_comm] using hx
      have hz' : z = 1 := by simpa only [finRotate_last,hFhead,Fin.val_zero,pow_zero,
        Option.mem_some_iff,eq_comm] using hz
      exact ⟨a,ha,by rw [hx',hz',inv_mul_cancel]⟩
  obtain ⟨C,hClen,_,hCword⟩ := cycle_of_disjoint_segments (by omega : 2 ≤ n+2)
    F hFne hFnd hdis hFc hjoin
  have hfirst : ∀ i : Fin (n+1), F i.castSucc = P.map (fun x => y^i.val*x) := by
    intro i
    have he : ¬ i.val = n+1 := by omega
    simp only [F,Fin.val_castSucc,he,ite_false]
  have hlength : (n+1)*Nat.card H+1 ≤ C.length := by
    rw [hClen,Fin.sum_univ_castSucc]
    have hf : (∑ i : Fin (n+1), (F i.castSucc).length) = (n+1)*Nat.card H := by
      simp only [hfirst,List.length_map,subgroup_enumeration_length H P hnd hmem]
      simp
    rw [hf]
    have he := List.length_pos_iff.mpr (hFne (Fin.last (n+1)))
    omega
  refine ⟨C,y,hqy,?_,?_⟩
  · change (orderOf (q a)-1)*Nat.card H+1 ≤ C.length
    simpa only [hn,show n+2-1 = n+1 by omega] using hlength
  · intro i hi u
    change i < orderOf (q a)-1 at hi
    have hi' : i < n+1 := by simpa only [hn,show n+2-1 = n+1 by omega] using hi
    rw [hCword,List.ofFn_succ',List.concat_eq_append,List.flatten_append,List.flatten_cons,List.flatten_nil,
      List.append_nil,List.dropLast_append_of_ne_nil (hFne (Fin.last (n+1)))]
    apply List.mem_append_left
    apply List.mem_flatten.mpr
    refine ⟨F (⟨i,hi'⟩ : Fin (n+1)).castSucc,List.mem_ofFn.mpr ⟨⟨i,hi'⟩,rfl⟩,?_⟩
    rw [hfirst]
    exact List.mem_map.mpr ⟨u.val,(hmem u.val).mpr u.property,rfl⟩

end DirectedCycles
