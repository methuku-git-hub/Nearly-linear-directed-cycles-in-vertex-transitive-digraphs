import DirectedCycles.LayerWordReplacement

set_option autoImplicit false
namespace DirectedCycles

/-- A baseline word or a word obtained by changing one baseline label. -/
def SingleChangeWord {G : Type*} (xs ys : List G) : Prop :=
  ys = xs ∨ ∃ j : Fin xs.length, ∃ a : G, ys = xs.set j.val a

/-- Products of the baseline and all allowed single-change full rounds. -/
def singleRoundProducts {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (xs : List G) : Set G :=
  {g | ∃ ys : List G, SingleChangeWord xs ys ∧ LayerWord S 0 ys ∧ ys.prod = g}

theorem SingleChangeWord.length {G : Type*} {xs ys : List G} (h : SingleChangeWord xs ys) :
    ys.length = xs.length := by
  rcases h with rfl | ⟨j,a,rfl⟩ <;> simp

/-- Before the changed entry a prefix is unchanged; after it, its change is
the same left multiplier as that of the full product. -/
theorem singleChangeWord_prefix {G : Type*} [Group G] (xs ys : List G)
    (h : SingleChangeWord xs ys) (k : ℕ) (hk : k ≤ xs.length) :
    (ys.take k).prod = (xs.take k).prod ∨
      (ys.take k).prod = ys.prod*xs.prod⁻¹*(xs.take k).prod := by
  rcases h with rfl | ⟨j,a,rfl⟩
  · exact Or.inl rfl
  · by_cases hj : k ≤ j.val
    · exact Or.inl (by rw [List.take_set_of_le hj])
    · right
      have hjk : j.val < (xs.take k).length := by
        rw [List.length_take,Nat.min_eq_left hk]
        omega
      rw [List.take_set,list_product_replacement (xs.take k) j.val hjk a]
      rw [List.take_take,Nat.min_eq_left (by omega : j.val ≤ k),List.getElem_take,
        list_product_replacement xs j.val j.isLt a]
      group

/-- The baseline and its one-position changes generate every full-round
product. The prefix correction proof works in noncommutative groups. -/
theorem singleRoundProducts_generate {G : Type*} [Group G] {T : ℕ}
    (S : ZMod T → Set G) (xs : List G) (hlen : xs.length = T)
    (hxs : LayerWord S 0 xs) :
    Subgroup.closure (singleRoundProducts S xs) = Subgroup.closure (layerRoundProducts S) := by
  let C := Subgroup.closure (singleRoundProducts S xs)
  have ht : xs.prod ∈ C := Subgroup.subset_closure ⟨xs,Or.inl rfl,hxs,rfl⟩
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro g ⟨ys,hys,hallowed,rfl⟩
    exact ⟨ys,hys.length.trans hlen,hallowed,rfl⟩
  · apply C.closure_le.mpr
    rintro g ⟨ys,hylen,hy,rfl⟩
    have hp : ∀ k : ℕ, k ≤ xs.length → (ys.take k).prod*((xs.take k).prod)⁻¹ ∈ C := by
      intro k hk
      induction k with
      | zero => simp only [List.take_zero,List.prod_nil,inv_one,mul_one]; exact C.one_mem
      | succ k ih =>
        have hkx : k < xs.length := by omega
        have hky : k < ys.length := by omega
        have hm : (xs.set k ys[k]).prod ∈ C := by
          apply Subgroup.subset_closure
          refine ⟨xs.set k ys[k],Or.inr ⟨⟨k,hkx⟩,ys[k],rfl⟩,?_,rfl⟩
          apply layerWord_set S 0 xs hxs k ys[k]
          exact (layerWord_iff_get S 0 ys).mp hy ⟨k,hky⟩
        have hrel := C.mul_mem hm (C.inv_mem ht)
        have hstep := C.mul_mem (ih (by omega)) hrel
        rw [list_product_replacement xs k hkx ys[k]] at hstep
        have htx : (xs.take (k+1)).prod = (xs.take k).prod*xs[k] := by
          rw [← List.take_concat_get' xs k hkx,List.prod_append,List.prod_singleton]
        have hty : (ys.take (k+1)).prod = (ys.take k).prod*ys[k] := by
          rw [← List.take_concat_get' ys k hky,List.prod_append,List.prod_singleton]
        rw [htx,hty]
        convert hstep using 1
        group
    have h := C.mul_mem (hp xs.length le_rfl) ht
    have he : ys.take xs.length = ys := List.take_of_length_le (by omega)
    change ys.prod ∈ C
    simpa only [he,List.take_length,inv_mul_cancel_right] using h

end DirectedCycles
